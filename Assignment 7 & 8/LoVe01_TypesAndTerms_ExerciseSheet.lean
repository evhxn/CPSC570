/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun a _ ↦ a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun _ a ↦ a

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun _ _ g _ ↦ g _
  -- Alternatively: fun f a g b ↦ f a b

/- Actually, let's be more careful. The type is
   (α → β → γ) → α → (α → γ) → β → γ
   We need to produce a γ. We have:
     f : α → β → γ
     a : α
     g : α → γ
     b : β
   Several ways to get γ: f a b, or g a. Both work. -/

-- Overwrite with a clean version:

def someNonsense' : (α → β → γ) → α → (α → γ) → β → γ :=
  fun f a _g b ↦ f a b


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. -/

/-
  C := fun f b a ↦ f a b

  Derivation:

  Let Γ = f : α → β → γ, b : β, a : α

                     ————————————————— Var    ————————— Var
                     Γ ⊢ f : α → β → γ       Γ ⊢ a : α
                     ————————————————————————————————————— App
              ————————— Var        Γ ⊢ f a : β → γ               ————————— Var
              Γ ⊢ b : β                                          Γ ⊢ b : β
              —————————————————————————————————————————————————————————————— App
                                  Γ ⊢ f a b : γ
  ——————————————————————————————————————————————————————————————————————————————— Abs (a)
            f : α → β → γ, b : β ⊢ (fun a ↦ f a b) : α → γ
  ——————————————————————————————————————————————————————————————————————————————— Abs (b)
            f : α → β → γ ⊢ (fun b a ↦ f a b) : β → α → γ
  ——————————————————————————————————————————————————————————————————————————————— Abs (f)
            ⊢ (fun f b a ↦ f a b) : (α → β → γ) → β → α → γ
-/

end LoVe
