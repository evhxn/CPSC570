# Assignment 6: Verified Transactional Inventory

**CPSC 570: From Bugs to Proofs** · Chapman University · Spring 2026

Deductive verification of a transactional inventory system in Dafny. The assignment covers object invariants, pre/postconditions, loop invariants with termination, and helper lemmas for recursive sequence properties.

---

## Scenario

A backend inventory component exposes three operations:

- `Reserve(qty)` — tentatively reserve stock
- `CommitOne()` / `CommitAllPending()` — commit pending reservations
- `RollbackAll()` — discard all pending reservations

**Business rule:** committed + pending stock must never exceed total stock at any point.

---

## Files

| File | Description |
|------|-------------|
| `homework-transactions.dfy` | Single Dafny file containing all three parts — specs/contracts, loop invariants, and helper lemmas |

---

## Structure

### Part 1 — Preconditions, Postconditions, and Object Validity

`Valid()` is strengthened to enforce the core business invariant: `committed <= total` and `committed + PendingSum(reservedLog) <= total`. The constructor, `Reserve`, and `RollbackAll` are annotated with full pre/postcondition contracts covering validity preservation, field immutability, and the success/failure behavior of the reservation log.

### Part 2 — Loop Invariants and Termination

`CommitAllPending()` is verified with five loop invariants: index bounds, accumulator correctness (prefix sum), field stability during iteration, capacity safety, and total immutability. The termination measure is `|pending| - i`. `PendingSumConcat` is called inline to help Dafny extend the prefix invariant one step at a time.

### Part 3 — Helper Lemmas

Three lemmas support the proof infrastructure:

- `PendingSumConcat` — proves `PendingSum` distributes over concatenation by structural induction on `xs`
- `PrefixBound` — proves a prefix sum never exceeds the full sum, using `PendingSumConcat` and nat non-negativity
- `PrefixCommit` — iteratively accumulates a k-element prefix sum and uses `PrefixBound` to discharge the bound postcondition

---

## Running

```bash
dafny verify homework-transactions.dfy
```

Expected output: all methods and lemmas verify with no errors.

A VS Code setup is also supported via the [Dafny extension](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode) — open the file and errors will appear inline.

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
