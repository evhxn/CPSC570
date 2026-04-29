/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 3 (10 points): Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (5 points): Connectives and Quantifiers -/

/- 1.1 (4 points). -/

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b := by
  intro hab hca hc
  exact hab (hca hc)

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c := by
  intro habc hab ha
  exact habc ha (hab ha)

theorem more_nonsense (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d := by
  intro hf hc hb
  apply hf
  · intro _
    exact hb
  · exact hc

theorem even_more_nonsense (a b c : Prop) :
    (a → b) → (a → c) → a → b → c := by
  intro _hab hac ha _hb
  exact hac ha

/- 1.2 (1 point). -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b := by
  intro hf
  apply hf
  intro hg
  apply hg
  intro ha
  apply hf
  intro _
  exact ha


/- ## Question 2 (5 points): Logical Connectives -/

/- 2.1 (1 point). -/

theorem herman (a : Prop) :
    ¬¬ (¬¬ a → a) := by
  intro h
  apply h
  intro hna
  exact False.elim (hna (fun ha ↦ False.elim (h (fun _ ↦ ha))))

/- 2.2 (2 points). -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle := by
  rw [DoubleNegation, ExcludedMiddle]
  intro hdn a
  apply hdn
  intro hnem
  apply hnem
  right
  intro ha
  apply hnem
  left
  exact ha

/- 2.3 (2 points). State and prove the three missing implications. -/

-- DN → Peirce (via DN → EM → Peirce)
theorem Peirce_of_DN :
    DoubleNegation → Peirce := by
  intro hdn
  exact Peirce_of_EM (EM_of_DN hdn)

-- EM → DN (via EM → Peirce → DN)
theorem DN_of_EM :
    ExcludedMiddle → DoubleNegation := by
  intro hem
  exact DN_of_Peirce (Peirce_of_EM hem)

-- Peirce → EM (via Peirce → DN → EM)
theorem EM_of_Peirce :
    Peirce → ExcludedMiddle := by
  intro hp
  exact EM_of_DN (DN_of_Peirce hp)

end BackwardProofs

end LoVe
