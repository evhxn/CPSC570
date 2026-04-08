// Transactional Inventory Homework (single file, no repeated definitions)
// CPSC 570: From Bugs to Proofs

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

  // Captures the business rule:
  // 1) committed never exceeds total
  // 2) committed + pending never exceeds total
  predicate Valid()
    reads this
  {
    committed <= total &&
    committed + PendingSum(reservedLog) <= total
  }

  constructor Init(initialTotal: nat)
    ensures total == initialTotal
    ensures committed == 0
    ensures reservedLog == []
    ensures Valid()
  {
    total := initialTotal;
    committed := 0;
    reservedLog := [];
  }

  method Reserve(qty: nat) returns (ok: bool)
    requires Valid()
    modifies this
    ensures Valid()
    ensures total == old(total)
    ensures committed == old(committed)
    // Capacity-permits success: if there's room, the call succeeds.
    ensures (old(committed) + PendingSum(old(reservedLog)) + qty <= total) ==> ok
    // On success: append the reservation to the log
    ensures ok ==> reservedLog == old(reservedLog) + [qty]
    // On failure: log unchanged
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
    ensures Valid()
    ensures committed == old(committed)
    ensures total == old(total)
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
    ensures total == old(total)
  {
    var startCommitted := committed;
    var pending := reservedLog;
    var i := 0;
    var newlyCommitted := 0;

    while i < |pending|
      // 1) Loop index is in valid bounds
      invariant 0 <= i <= |pending|
      // 2) Accumulator equals sum of the prefix processed so far
      invariant newlyCommitted == PendingSum(pending[..i])
      // 3) The field `committed` is unchanged during the loop body
      invariant committed == startCommitted
      // 4) Total inventory unchanged from method entry
      invariant total == old(total)
      // 5) Pending list and reservedLog unchanged during the loop
      invariant pending == old(reservedLog)
      invariant reservedLog == old(reservedLog)
      // 6) The original committed amount plus the full pending total fits in capacity
      //    (this is what Valid() gave us at entry, and it's still true)
      invariant startCommitted + PendingSum(pending) <= total
      decreases |pending| - i
    {
      // Lemma application: extending the prefix by one element extends the sum
      // by that element. This follows from PendingSumConcat.
      PendingSumPrefixStep(pending, i);
      newlyCommitted := newlyCommitted + pending[i];
      i := i + 1;
    }

    // After the loop, i == |pending|, so pending[..i] == pending
    assert pending[..i] == pending;
    assert newlyCommitted == PendingSum(pending);

    committed := startCommitted + newlyCommitted;
    reservedLog := [];
  }
}

// =========================
// Part 3: Lemmas and Proof Reuse
// =========================

// Part 3.1: PendingSum distributes over concatenation.
lemma PendingSumConcat(xs: seq<nat>, ys: seq<nat>)
  ensures PendingSum(xs + ys) == PendingSum(xs) + PendingSum(ys)
  decreases |xs|
{
  if |xs| == 0 {
    // Base case: xs == [], so xs + ys == ys, and PendingSum([]) == 0.
    assert xs + ys == ys;
  } else {
    // Inductive case. Show that (xs + ys)[1..] == xs[1..] + ys.
    assert (xs + ys)[0] == xs[0];
    assert (xs + ys)[1..] == xs[1..] + ys;
    PendingSumConcat(xs[1..], ys);
  }
}

// Part 3.2: A prefix sum is never larger than the full sum.
lemma PrefixBound(xs: seq<nat>, i: nat)
  requires i <= |xs|
  ensures PendingSum(xs[..i]) <= PendingSum(xs)
{
  // The full sequence is the prefix concatenated with the suffix.
  assert xs == xs[..i] + xs[i..];
  PendingSumConcat(xs[..i], xs[i..]);
  // Now PendingSum(xs) == PendingSum(xs[..i]) + PendingSum(xs[i..])
  // Since PendingSum returns nat, PendingSum(xs[i..]) >= 0, so the bound holds.
}

// Helper lemma used by CommitAllPending: the sum of the (i+1)-prefix
// equals the sum of the i-prefix plus the i-th element. This is the
// "extend prefix by one" step that the loop body needs.
lemma PendingSumPrefixStep(xs: seq<nat>, i: nat)
  requires i < |xs|
  ensures PendingSum(xs[..i+1]) == PendingSum(xs[..i]) + xs[i]
{
  // xs[..i+1] == xs[..i] + [xs[i]]
  assert xs[..i+1] == xs[..i] + [xs[i]];
  PendingSumConcat(xs[..i], [xs[i]]);
  // PendingSum([xs[i]]) == xs[i] + PendingSum([]) == xs[i]
  assert PendingSum([xs[i]]) == xs[i];
}

// Part 3.3: Use the lemmas to finish the proof.
method PrefixCommit(pending: seq<nat>, k: nat) returns (taken: nat)
  requires k <= |pending|
  ensures taken == PendingSum(pending[..k])
  ensures taken <= PendingSum(pending)
{
  var i := 0;
  taken := 0;
  while i < k
    invariant 0 <= i <= k
    invariant taken == PendingSum(pending[..i])
    decreases k - i
  {
    PendingSumPrefixStep(pending, i);
    taken := taken + pending[i];
    i := i + 1;
  }

  // After the loop, i == k, so taken == PendingSum(pending[..k])
  assert taken == PendingSum(pending[..k]);

  // Use PrefixBound to conclude taken <= PendingSum(pending)
  PrefixBound(pending, k);
}
