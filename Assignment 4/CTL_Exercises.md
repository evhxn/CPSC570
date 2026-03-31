# CTL Exercises -- Solutions

## Exercise 1: Semantics of CTL modalities

Let ρ = s₀s₁s₂… be a path.

### 1. Prove: ρ ⊨ ◇Φ iff there exists some j ≥ 0 such that sⱼ ⊨ Φ

**Proof.**

By definition, ◇Φ = ⊤ U Φ.

By the semantics of U: ρ ⊨ Φ₁ U Φ₂ iff there exists j ≥ 0 such that ρ[j] ⊨ Φ₂ and for all 0 ≤ k < j: ρ[k] ⊨ Φ₁.

Applying this to ◇Φ = ⊤ U Φ:

ρ ⊨ ⊤ U Φ iff there exists j ≥ 0 such that ρ[j] ⊨ Φ and for all 0 ≤ k < j: ρ[k] ⊨ ⊤.

Since ρ[k] ⊨ ⊤ for every state (⊤ is always true), the second condition is trivially satisfied.

Therefore: ρ ⊨ ◇Φ iff there exists j ≥ 0 such that sⱼ ⊨ Φ. ∎


### 2. Prove: s ⊨ ∃□Φ iff there is a path ρ ∈ Path(s) such that ρ[j] ⊨ Φ for all j ≥ 0

**Proof.**

By definition, ∃□Φ = ¬∀◇¬Φ.

(⇒) Assume s ⊨ ∃□Φ, i.e., s ⊨ ¬∀◇¬Φ. Then s ⊭ ∀◇¬Φ.

By the semantics of ∀: s ⊨ ∀φ iff for all ρ ∈ Path(s): ρ ⊨ φ.

So s ⊭ ∀◇¬Φ means it is not the case that for all ρ ∈ Path(s): ρ ⊨ ◇¬Φ.

Therefore, there exists some ρ ∈ Path(s) such that ρ ⊭ ◇¬Φ.

By part 1, ρ ⊨ ◇¬Φ iff there exists j ≥ 0 with ρ[j] ⊨ ¬Φ. So ρ ⊭ ◇¬Φ means there is no j ≥ 0 with ρ[j] ⊨ ¬Φ, i.e., for all j ≥ 0: ρ[j] ⊨ Φ.

So there exists ρ ∈ Path(s) such that ρ[j] ⊨ Φ for all j ≥ 0.

(⇐) Assume there exists ρ ∈ Path(s) with ρ[j] ⊨ Φ for all j ≥ 0.

Then for all j ≥ 0: ρ[j] ⊭ ¬Φ, so there is no j ≥ 0 with ρ[j] ⊨ ¬Φ.

By part 1, ρ ⊭ ◇¬Φ.

So it is not the case that all paths from s satisfy ◇¬Φ, meaning s ⊭ ∀◇¬Φ.

Therefore s ⊨ ¬∀◇¬Φ = ∃□Φ. ∎


### 3. Prove: s ⊨ ∀□Φ iff for all paths ρ ∈ Path(s): ρ[j] ⊨ Φ for all j ≥ 0

**Proof.**

By definition, ∀□Φ = ¬∃◇¬Φ.

(⇒) Assume s ⊨ ∀□Φ, i.e., s ⊨ ¬∃◇¬Φ. Then s ⊭ ∃◇¬Φ.

By the semantics of ∃: s ⊨ ∃φ iff there exists ρ ∈ Path(s) with ρ ⊨ φ.

So s ⊭ ∃◇¬Φ means there is no ρ ∈ Path(s) with ρ ⊨ ◇¬Φ.

Equivalently, for all ρ ∈ Path(s): ρ ⊭ ◇¬Φ.

By part 1, ρ ⊭ ◇¬Φ means there is no j ≥ 0 with ρ[j] ⊨ ¬Φ, i.e., for all j ≥ 0: ρ[j] ⊨ Φ.

So for all ρ ∈ Path(s), for all j ≥ 0: ρ[j] ⊨ Φ.

(⇐) Assume for all ρ ∈ Path(s), for all j ≥ 0: ρ[j] ⊨ Φ.

Then for every ρ, there is no j with ρ[j] ⊨ ¬Φ, so ρ ⊭ ◇¬Φ for every ρ.

Hence there is no ρ ∈ Path(s) with ρ ⊨ ◇¬Φ, so s ⊭ ∃◇¬Φ.

Therefore s ⊨ ¬∃◇¬Φ = ∀□Φ. ∎


---

## Exercise 2: CTL properties of transition systems

**The transition system T:**
- States: S = {s₀, s₁, s₂, s₃}
- Initial state: I = {s₀}
- Transitions: s₀→s₁, s₀→s₂, s₁→s₃, s₃→s₃ (self-loop), s₃→s₁
- Labels: λ(s₀) = {a}, λ(s₁) = {a,b}, λ(s₂) = {b}, λ(s₃) = {a}

### 1. ∃○a — "there exists a successor where a holds"

For each state, we check: is there some successor where a holds?

- **s₀:** successors are s₁ and s₂. s₁ ⊨ a (since a ∈ {a,b}). So **s₀ ⊨ ∃○a**. ✓
- **s₁:** successor is s₃. s₃ ⊨ a (since a ∈ {a}). So **s₁ ⊨ ∃○a**. ✓
- **s₂:** s₂ has no outgoing edges shown in the diagram (it is a terminal-like state, but the system has no terminal states — so we must assume s₂ has a self-loop or the system is restricted). If s₂ has no successors, the formula is vacuously true. If s₂ has a self-loop, then its only successor is s₂ with label {b}, so a ∉ {b} and **s₂ ⊭ ∃○a**. ✗
- **s₃:** successors are s₃ and s₁. s₃ ⊨ a and s₁ ⊨ a. So **s₃ ⊨ ∃○a**. ✓

**Does T satisfy ∃○a?** We need s₀ ⊨ ∃○a. Yes, since s₁ is a successor of s₀ and a ∈ λ(s₁). **T ⊨ ∃○a. TRUE.** ✓


### 2. ∀□a — "on all paths, a holds in every state"

We need: for all paths from a state, a holds at every position.

- **s₀:** λ(s₀) = {a}, so a holds at s₀. But consider the path s₀ → s₂. λ(s₂) = {b}, and a ∉ {b}. So there exists a path from s₀ where a fails at position 1. **s₀ ⊭ ∀□a**. ✗
- **s₁:** path s₁ → s₃ → s₃ → … has a holding everywhere. Path s₁ → s₃ → s₁ → s₃ → … also has a everywhere. All paths from s₁ go to s₃ (the only successor), and from s₃ we can only go to s₃ or s₁, both of which satisfy a. **s₁ ⊨ ∀□a**. ✓
- **s₂:** a ∉ λ(s₂), so a doesn't even hold at s₂ itself. **s₂ ⊭ ∀□a**. ✗
- **s₃:** all paths from s₃ visit only s₃ and s₁, both of which satisfy a. **s₃ ⊨ ∀□a**. ✓

**Does T satisfy ∀□a?** We need s₀ ⊨ ∀□a. No, since the path s₀ → s₂ has a failing at s₂. **T ⊨ ∀□a. FALSE.** ✗


### 3. ∃◇(∃□a) — "there exists a path to a state from which some path always satisfies a"

First, identify which states satisfy ∃□a (there exists a path from that state where a holds forever):

- **s₀:** path s₀ → s₁ → s₃ → s₃ → … has a at every state. **s₀ ⊨ ∃□a**. ✓
- **s₁:** path s₁ → s₃ → s₃ → … has a everywhere. **s₁ ⊨ ∃□a**. ✓
- **s₂:** a ∉ λ(s₂), so a fails immediately on any path from s₂. **s₂ ⊭ ∃□a**. ✗
- **s₃:** path s₃ → s₃ → s₃ → … has a everywhere. **s₃ ⊨ ∃□a**. ✓

Now, ∃◇(∃□a) asks: is there a path from a state that eventually reaches a state satisfying ∃□a?

- **s₀:** path s₀ → s₁ reaches s₁, and s₁ ⊨ ∃□a. (In fact, s₀ itself satisfies ∃□a.) **s₀ ⊨ ∃◇(∃□a)**. ✓
- **s₁:** s₁ ⊨ ∃□a, so trivially s₁ ⊨ ∃◇(∃□a) (take j=0). **s₁ ⊨ ∃◇(∃□a)**. ✓
- **s₂:** if s₂ has only a self-loop, then all paths stay at s₂, and s₂ ⊭ ∃□a, so ∃◇(∃□a) fails. **s₂ ⊭ ∃◇(∃□a)**. ✗
- **s₃:** s₃ ⊨ ∃□a, so trivially **s₃ ⊨ ∃◇(∃□a)**. ✓

**Does T satisfy ∃◇(∃□a)?** We need s₀ ⊨ ∃◇(∃□a). Yes, since s₀ itself satisfies ∃□a (via path s₀ → s₁ → s₃ → s₃ → …). **T ⊨ ∃◇(∃□a). TRUE.** ✓
