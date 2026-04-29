/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers -/

theorem I (a : Prop) :
    a → a := by
  intro ha
  exact ha

theorem K (a b : Prop) :
    a → b → b := by
  intro _ha hb
  exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c := by
  intro hf hb ha
  exact hf ha hb

theorem proj_fst (a : Prop) :
    a → a → a := by
  intro ha _
  exact ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a := by
  intro _ ha
  exact ha

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c := by
  intro hf ha _hg _hb
  exact hf ha _hb

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a := by
  intro hab hnb ha
  exact hnb (hab ha)

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro ⟨hp, hq⟩ x
    exact ⟨hp x, hq x⟩


/- ## Question 2: Natural Numbers -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 := by
  rfl

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n := by
  rfl

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := by
  induction m with
  | zero =>
    simp [mul, mul_zero]
    induction n with
    | zero => rfl
    | succ n ih => simp [mul, add, ih]
  | succ m ih =>
    simp [mul]
    rw [ih]
    induction n with
    | zero => simp [mul, add]
    | succ n ihn =>
      simp [mul, add]
      rw [← ihn]
      simp [mul, add]
      ring

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := by
  induction l with
  | zero => simp [mul]
  | succ l ih =>
    simp [mul]
    rw [ih]
    simp [mul_add]

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) := by
  rw [mul_comm (add l m) n]
  rw [mul_add]
  rw [mul_comm n l, mul_comm n m]


/- ## Question 3: Intuitionistic Logic -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce := by
  rw [ExcludedMiddle, Peirce]
  intro hem a b hf
  have h := hem a
  cases h with
  | inl ha => exact ha
  | inr hna =>
    apply hf
    intro ha
    exact False.elim (hna ha)

theorem DN_of_Peirce :
    Peirce → DoubleNegation := by
  rw [Peirce, DoubleNegation]
  intro hpeirce a hnna
  apply hpeirce a False
  intro haf
  exact False.elim (hnna haf)

namespace SorryTheorems

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

end SorryTheorems

end BackwardProofs

end LoVe
