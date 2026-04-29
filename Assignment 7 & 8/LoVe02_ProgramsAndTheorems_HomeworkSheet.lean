/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Snoc -/

/- 1.1 (3 points). Define `snoc` by recursion (no `++`). -/

def snoc {α : Type} : List α → α → List α
  | [],      a => [a]
  | x :: xs, a => x :: snoc xs a

/- 1.2 (1 point). Test snoc. -/

#eval snoc [1] 2         -- expected: [1, 2]
#eval snoc [] 42         -- expected: [42]
#eval snoc [1, 2, 3] 4   -- expected: [1, 2, 3, 4]


/- ## Question 2 (6 points): Sum -/

/- 2.1 (3 points). Define `sum`. -/

def sum : List ℕ → ℕ
  | []      => 0
  | x :: xs => x + sum xs

#eval sum [1, 12, 3]   -- expected: 16

/- 2.2 (3 points). State properties of `sum`. -/

theorem sum_snoc (ms : List ℕ) (n : ℕ) :
    sum (snoc ms n) = n + sum ms :=
  sorry

theorem sum_append (ms ns : List ℕ) :
    sum (ms ++ ns) = sum ms + sum ns :=
  sorry

theorem sum_reverse (ns : List ℕ) :
    sum (ns.reverse) = sum ns :=
  sorry

end LoVe
