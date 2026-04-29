# Logical Verification in Lean 4 (Exercises 1-3 & Homework 1-3)

## Overview

Solutions for Exercise Sheets 1-3 and Homework Sheets 1-3 from the [Logical Verification](https://github.com/lean-forward/logical_verification_2025) course, implemented in Lean 4.

## Files

### Exercise Sheets (HW 7)

| File | Topic | Key Concepts |
|------|-------|--------------|
| `LoVe01_TypesAndTerms_ExerciseSheet.lean` | Types and Terms | Combinators (I, K, C), typing derivations |
| `LoVe02_ProgramsAndTheorems_ExerciseSheet.lean` | Programs and Theorems | Predecessor, AExp simplification, map, correctness statements |
| `LoVe03_BackwardProofs_ExerciseSheet.lean` | Backward Proofs | Tactic proofs (intro, apply, exact), induction, classical logic |

### Homework Sheets (HW 8)

| File | Topic | Key Concepts |
|------|-------|--------------|
| `LoVe01_TypesAndTerms_HomeworkSheet.lean` | Types and Terms | B, S combinators, weakPeirce, typing derivation |
| `LoVe02_ProgramsAndTheorems_HomeworkSheet.lean` | Programs and Theorems | snoc, sum, theorem statements |
| `LoVe03_BackwardProofs_HomeworkSheet.lean` | Backward Proofs | weak_peirce, herman, EM/DN/Peirce equivalence chain |

## How to Run

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) with `elan` and `lake`
- The [logical_verification_2025](https://github.com/lean-forward/logical_verification_2025) project cloned locally

### Steps

1. Clone the LoVe project:
   ```bash
   git clone https://github.com/lean-forward/logical_verification_2025.git
   cd logical_verification_2025
   ```

2. Copy the completed `.lean` files into the `lean/LoVe/` directory, replacing the originals.

3. Build and check:
   ```bash
   lake build
   ```

4. Or open individual files in VSCode with the Lean 4 extension. Errors/warnings appear inline.

### Verification

All definitions and proofs should compile without `sorry` errors, except for theorem *statements* in Exercise 2 and Homework 2 where `sorry` is intentionally used as the proof body.
