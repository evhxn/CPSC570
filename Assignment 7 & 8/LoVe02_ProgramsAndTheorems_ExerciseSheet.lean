/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Exercise 2: Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Predecessor Function -/

def pred : ℕ → ℕ
  | 0          => 0
  | Nat.succ n => n

#eval pred 0    -- expected: 0
#eval pred 1    -- expected: 0
#eval pred 2    -- expected: 1
#eval pred 3    -- expected: 2
#eval pred 10   -- expected: 9
#eval pred 99   -- expected: 98


/- ## Question 2: Arithmetic Expressions -/

#check AExp
#check eval

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- expected: 3
#eval eval someEnv (AExp.num 42)    -- expected: 42
#eval eval someEnv (AExp.add (AExp.var "x") (AExp.var "y"))  -- expected: 20
#eval eval someEnv (AExp.sub (AExp.num 10) (AExp.num 3))     -- expected: 7
#eval eval someEnv (AExp.mul (AExp.num 2) (AExp.var "x"))    -- expected: 6
#eval eval someEnv (AExp.div (AExp.num 10) (AExp.num 3))     -- expected: 3
#eval eval someEnv (AExp.div (AExp.num 10) (AExp.num 0))     -- division by zero

/- 2.2. Simplify arithmetic expressions involving all four operators. -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  | AExp.sub e₁ (AExp.num 0) => simplify e₁
  | AExp.mul (AExp.num 0) _  => AExp.num 0
  | AExp.mul _ (AExp.num 0)  => AExp.num 0
  | AExp.mul (AExp.num 1) e₂ => simplify e₂
  | AExp.mul e₁ (AExp.num 1) => simplify e₁
  | AExp.div e₁ (AExp.num 1) => simplify e₁
  -- catch-all cases below
  | AExp.num i               => AExp.num i
  | AExp.var x               => AExp.var x
  | AExp.add e₁ e₂           => AExp.add (simplify e₁) (simplify e₂)
  | AExp.sub e₁ e₂           => AExp.sub (simplify e₁) (simplify e₂)
  | AExp.mul e₁ e₂           => AExp.mul (simplify e₁) (simplify e₂)
  | AExp.div e₁ e₂           => AExp.div (simplify e₁) (simplify e₂)

/- 2.3. State the correctness property of simplify. -/

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  eval env (simplify e) = eval env e :=
  sorry


/- ## Question 3: Map -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

#eval map (fun n ↦ n + 10) [1, 2, 3]   -- expected: [11, 12, 13]

/- Functorial properties of map -/

theorem map_identity {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  sorry

theorem map_composition {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    map (fun x ↦ g (f x)) xs = map g (map f xs) :=
  sorry

end LoVe
