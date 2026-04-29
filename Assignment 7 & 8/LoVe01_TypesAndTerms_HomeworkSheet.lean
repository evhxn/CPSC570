/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 1 (10 points): Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Terms -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1 (4 points). Complete the following definitions. -/

def B : (α → β) → (γ → α) → γ → β :=
  fun f g c ↦ f (g c)

def S : (α → β → γ) → (α → β) → α → γ :=
  fun f g a ↦ f a (g a)

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  fun f c _b ↦ f (fun _ ↦ _b) c

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  fun _f g a _b ↦ g a

/- 1.2 (2 points). -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  fun f ↦ f (fun g ↦ g (fun a ↦ f (fun _ ↦ a)))

/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above. -/

/-
  B := fun f g c ↦ f (g c)

  Let Γ = f : α → β, g : γ → α, c : γ

                     ————————————————— Var    ————————— Var
                     Γ ⊢ g : γ → α           Γ ⊢ c : γ
                     ———————————————————————————————————— App
  ————————————————— Var         Γ ⊢ g c : α
  Γ ⊢ f : α → β
  ——————————————————————————————————————————————————————— App
                     Γ ⊢ f (g c) : β
  ——————————————————————————————————————————————————————— Abs (c)
            f : α → β, g : γ → α ⊢ (fun c ↦ f (g c)) : γ → β
  ——————————————————————————————————————————————————————— Abs (g)
            f : α → β ⊢ (fun g c ↦ f (g c)) : (γ → α) → γ → β
  ——————————————————————————————————————————————————————— Abs (f)
            ⊢ (fun f g c ↦ f (g c)) : (α → β) → (γ → α) → γ → β
-/

end LoVe
