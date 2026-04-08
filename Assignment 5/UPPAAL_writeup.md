# UPPAAL Train-Gate Homework Writeup

## Q1: Queue Invariant (CTL Safety)

**Property:**
```
A[] forall (i : id_t) Train(i).Cross imply Gate.len >= 1
```

**Result:** Verified — **satisfied**.

**Explanation.** This property holds because of how the gate's queue protocol works. A train can only enter `Cross` from one of two paths:
1. Directly from `Appr` via the guard `x >= 10` — but this transition is only enabled if the gate stayed `Free` long enough for the train not to be stopped, which happens when the gate handled its `appr[id]?` synchronization (transition from `Free` to `Occ` via the `enqueue(e)` action).
2. From `Start` via the guard `x >= 7` — which only happens after the train was stopped, then released by the gate via `go[front()]!`.

In both cases, the train was enqueued *before* it ever reached `Cross`. The gate dequeues a train only when it observes `leave[front()]?`, which fires *after* the train has already exited `Cross` (the `Cross → Safe` transition synchronizes on `leave[id]!`). So while a train is in `Cross`, it has already been enqueued but has not yet been dequeued — meaning `Gate.len >= 1`.

## Q2: Approaching Implies No One Crossing (TCTL — expected to fail)

**Property:**
```
A[] Train(0).Appr imply forall (i : id_t) (i == 0 or not Train(i).Cross)
```

**Result:** Verified — **NOT satisfied** (counterexample found).

**Counterexample scenario.** Consider this execution:
1. Train(1) calls `appr[1]!`, gate goes `Free → Occ`, enqueues Train(1). Train(1) enters `Appr` with clock `x = 0`.
2. Time passes; Train(1)'s clock advances to `x >= 10`. Train(1) takes the `Appr → Cross` transition (resetting its clock).
3. Now Train(1) is in `Cross`. Train(1)'s clock is small (still in [0, 5] since `x <= 5` is the invariant on `Cross`).
4. Meanwhile, Train(0) calls `appr[0]!`. Since the gate is in `Occ`, it goes via the committed location: enqueue Train(0), then immediately send `stop[0]!`. But the `stop[id]?` transition for Train(0) has the guard `x <= 10` — this only fires if Train(0)'s clock has not yet reached 10.

Wait — the issue is more subtle. Train(0) takes the `Safe → Appr` transition, which resets its clock to 0. So at the moment Train(0) enters `Appr`, its clock is 0. Before Train(0)'s clock reaches 10, the gate has time to send the `stop[0]?` signal to push Train(0) into `Stop`. But there is a window where Train(0) is in `Appr` with `x` between 0 and 10, and during that window, **Train(1) can be in `Cross`** because Train(1) entered `Cross` before Train(0) ever approached.

So the counterexample is: Train(1) approached first, was enqueued, advanced through `Appr → Cross`. Then Train(0) approached, entered `Appr` with `x = 0`, but Train(1) is still in `Cross` (and has not yet left). The gate will eventually push Train(0) to `Stop`, but during the window before that happens, both `Train(0).Appr` and `Train(1).Cross` hold simultaneously — violating the property.

## Q3: Adding the Clock Constraint (TCTL — fix Q2)

**Property:**
```
A[] (Train(0).Appr and Train(0).x > 10) imply forall (i : id_t) (i == 0 or not Train(i).Cross)
```

**Result:** Verified — **satisfied**.

**Explanation.**

1. **What does `Train(0).x > 10` tell us about Train(0)'s history?** Look at the transitions out of `Appr`. There are two: `Appr → Cross` (guard `x >= 10`, takes the train out of `Appr`) and `Appr → Stop` (guard `x <= 10`, synchronizes on `stop[id]?`). If Train(0) is *still* in `Appr` and its clock has surpassed 10, then it must have *missed* both opportunities to leave: it didn't take `Appr → Stop` (because the gate never sent `stop[0]!`) and it hasn't yet taken `Appr → Cross` (we're still in `Appr`). The `stop[id]?` transition has the guard `x <= 10`, so once `x > 10`, that transition is forever disabled. The only way Train(0) can still be in `Appr` past `x = 10` is that no `stop` was ever sent.

2. **What does that imply about the gate when Train(0) approached?** A `stop` is only sent when a train approaches while the gate is `Occ` (or via the committed Occ → committed → Occ transition that sends `stop[tail()]!`). If the gate never sent `stop[0]!`, then when Train(0) called `appr[0]!`, the gate was `Free` (it took the `Free → Occ` transition with `len == 0` and just enqueued Train(0)). So Train(0) is the *only* entry in the queue at the moment it approached, and `Gate.len == 1` with `front() == 0`.

3. **Why does this guarantee no other train can be crossing?** From the protocol, a train can only be in `Cross` if it has been enqueued and not yet dequeued. If at the moment Train(0) approached the gate was `Free` and the queue was empty, then there is no train currently between "enqueued" and "dequeued" — i.e., **no train is in `Cross` at that moment**. After Train(0) is enqueued, any other train that approaches (going through `Occ → committed → Occ`) is sent to `Stop`, which means they enter the queue *behind* Train(0) and cannot reach `Cross` until Train(0) has been dequeued. Since dequeuing happens via `leave`, which fires after `Cross → Safe`, and Train(0) never crossed, no later train can have crossed either while Train(0) is still in `Appr`.

Combined: Train(0) being in `Appr` with `x > 10` means the gate was free when it arrived, no train was crossing then, and the FIFO ordering ensures no other train can have entered `Cross` since.
