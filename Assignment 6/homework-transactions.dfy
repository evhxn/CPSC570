// Transactional Inventory Homework (single file, no repeated definitions)

function PendingSum(pending: seq<nat>): nat
  decreases |pending|
{
  if |pending| == 0 then 0 else pending[0] + PendingSum(pending[1..])
}

class InventoryAccount {
  var total: nat
  var committed: nat
  var reservedLog: seq<nat>

  // =========================
  // Part 1: Specs and Contracts
  // =========================

  // Valid captures the core business invariant:
  //   1) committed never exceeds total stock.
  //   2) committed + sum-of-pending never exceeds total stock.
  // (Invariant 1 is implied by 2 since PendingSum >= 0, but we state
  //  it explicitly so Dafny can use it directly without unfolding PendingSum.)
  predicate Valid()
    reads this
  {
    committed <= total &&
    committed + PendingSum(reservedLog) <= total
  }

  constructor Init(initialTotal: nat)
    ensures total == initialTotal   // 1) total is set to the supplied amount
    ensures committed == 0          // 2) nothing committed yet
    ensures reservedLog == []       // 3) no pending reservations
    ensures Valid()                 // 4) business rules hold from the start
  {
    total := initialTotal;
    committed := 0;
    reservedLog := [];
  }

  method Reserve(qty: nat) returns (ok: bool)
    requires Valid()
    modifies this
    // 1) Invariant is preserved regardless of outcome.
    ensures Valid()
    // 2) total and committed are never touched by Reserve.
    ensures total == old(total)
    ensures committed == old(committed)
    // 3a) If there was room for qty, we MUST report success.
    ensures old(committed) + PendingSum(old(reservedLog)) + qty <= old(total) ==> ok
    // 3b) On success, qty is appended to the log.
    ensures ok ==> reservedLog == old(reservedLog) + [qty]
    // 3c) On failure, the log is untouched.
    ensures !ok ==> reservedLog == old(reservedLog)
  {
    if committed + PendingSum(reservedLog) + qty <= total {
      reservedLog := reservedLog + [qty];
      ok := true;
    } else {
      ok := false;
    }
  }

  method RollbackAll()
    requires Valid()
    modifies this
    // Invariant is preserved (trivially: committed <= total, PendingSum([]) == 0).
    ensures Valid()
    // committed is untouched by a rollback.
    ensures committed == old(committed)
    // All pending reservations are discarded.
    ensures reservedLog == []
  {
    reservedLog := [];
  }

  // =========================
  // Part 2: Loop Invariants and Termination
  // =========================

  method CommitAllPending()
    requires Valid()
    modifies this
    ensures Valid()
    ensures reservedLog == []
    ensures committed == old(committed) + PendingSum(old(reservedLog))
  {
    var startCommitted := committed;
    var pending := reservedLog;
    var i := 0;
    var newlyCommitted := 0;

    while i < |pending|
      // 1) Loop index stays within [0, |pending|].
      invariant 0 <= i <= |pending|
      // 2) newlyCommitted equals the sum of the first i elements processed so far.
      invariant newlyCommitted == PendingSum(pending[..i])
      // 3) The field 'committed' itself is not updated inside the loop body;
      //    only the local accumulator newlyCommitted grows.
      invariant committed == startCommitted
      // 4) The final commit value will still fit within total capacity.
      //    (Follows from Valid() at entry: startCommitted + PendingSum(pending) <= total.)
      invariant startCommitted + PendingSum(pending) <= total
      // 5) Total inventory is constant throughout this method.
      invariant total == old(total)
      decreases |pending| - i
    {
      // Extend the prefix fact one step: pending[..i+1] == pending[..i] + [pending[i]]
      // Dafny needs help unfolding PendingSum for the new prefix.
      PendingSumConcat(pending[..i], [pending[i]]);
      assert pending[..i] + [pending[i]] == pending[..i+1];
      newlyCommitted := newlyCommitted + pending[i];
      i := i + 1;
    }

    // After the loop, i == |pending|, so pending[..i] == pending.
    assert pending[..i] == pending;
    committed := startCommitted + newlyCommitted;
    reservedLog := [];
  }
}

// =========================
// Part 3: Lemmas and Proof Reuse
// =========================

// Part 3.1 – PendingSum distributes over sequence concatenation.
// Proof: induction on |xs|.
//   Base: xs == [] so xs + ys == ys; PendingSum([]) == 0; 0 + PendingSum(ys) == PendingSum(ys). ✓
//   Step: xs == [h] + xs[1..].
//         PendingSum(xs + ys)
//           == xs[0] + PendingSum(xs[1..] + ys)   (unfold PendingSum once)
//           == xs[0] + PendingSum(xs[1..]) + PendingSum(ys)   (IH on xs[1..])
//           == PendingSum(xs) + PendingSum(ys). ✓
lemma PendingSumConcat(xs: seq<nat>, ys: seq<nat>)
  ensures PendingSum(xs + ys) == PendingSum(xs) + PendingSum(ys)
  decreases |xs|
{
  if |xs| == 0 {
    // Base case: [] + ys == ys, and PendingSum([]) == 0.
    assert xs + ys == ys;
  } else {
    // Give Dafny the association: (xs + ys)[1..] == xs[1..] + ys
    assert (xs + ys)[1..] == xs[1..] + ys;
    // Recursive call provides: PendingSum(xs[1..] + ys) == PendingSum(xs[1..]) + PendingSum(ys)
    PendingSumConcat(xs[1..], ys);
    // Dafny can now unfold PendingSum(xs + ys) == xs[0] + PendingSum(xs[1..] + ys)
    // and chain the equalities automatically.
  }
}

// Part 3.2 – A prefix sum never exceeds the full sum.
// Proof: xs == xs[..i] + xs[i..].
//        By PendingSumConcat: PendingSum(xs) == PendingSum(xs[..i]) + PendingSum(xs[i..]).
//        Since all elements are nat, PendingSum(xs[i..]) >= 0, so the inequality holds.
lemma PrefixBound(xs: seq<nat>, i: nat)
  requires i <= |xs|
  ensures PendingSum(xs[..i]) <= PendingSum(xs)
{
  // Reconstruct xs from its two halves, then apply concat lemma.
  assert xs == xs[..i] + xs[i..];
  PendingSumConcat(xs[..i], xs[i..]);
  // Now Dafny knows PendingSum(xs) == PendingSum(xs[..i]) + PendingSum(xs[i..])
  // and PendingSum(xs[i..]) >= 0 (nat), so the postcondition follows.
}

// Part 3.3 – Iteratively accumulate the first k elements, then prove the bound.
method PrefixCommit(pending: seq<nat>, k: nat) returns (taken: nat)
  requires k <= |pending|
  ensures taken == PendingSum(pending[..k])
  ensures taken <= PendingSum(pending)
{
  var i := 0;
  taken := 0;
  while i < k
    // Loop index stays in [0, k].
    invariant 0 <= i <= k
    // taken equals the sum of the first i elements.
    invariant taken == PendingSum(pending[..i])
    decreases k - i
  {
    // Extend the prefix by one: pending[..i+1] == pending[..i] + [pending[i]]
    PendingSumConcat(pending[..i], [pending[i]]);
    assert pending[..i] + [pending[i]] == pending[..i+1];
    taken := taken + pending[i];
    i := i + 1;
  }

  // After the loop, i == k, so pending[..i] == pending[..k].
  assert pending[..i] == pending[..k];

  // Use PrefixBound to discharge taken <= PendingSum(pending).
  PrefixBound(pending, k);
}
