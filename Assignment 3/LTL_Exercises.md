# LTL Exercises — Solutions

## Exercise 1: Semantics of temporal modalities

### 1. Prove: σ ⊨ □φ iff for all j ≥ 0 we have σ[j…] ⊨ φ

**Proof.**

By definition, □φ := ¬◇¬φ.

(⇒) Assume σ ⊨ □φ, i.e., σ ⊨ ¬◇¬φ. Then σ ⊭ ◇¬φ.

By the semantics of ◇: σ ⊨ ◇ψ iff there exists j ≥ 0 such that σ[j…] ⊨ ψ.

So σ ⊭ ◇¬φ means there is no j ≥ 0 with σ[j…] ⊨ ¬φ.

Equivalently, for all j ≥ 0 we have σ[j…] ⊭ ¬φ, which means for all j ≥ 0: σ[j…] ⊨ φ.

(⇐) Assume for all j ≥ 0: σ[j…] ⊨ φ.

Then for all j ≥ 0: σ[j…] ⊭ ¬φ.

So there is no j ≥ 0 with σ[j…] ⊨ ¬φ, meaning σ ⊭ ◇¬φ.

Therefore σ ⊨ ¬◇¬φ = □φ. ∎


### 2. Prove: σ ⊨ □◇φ iff for all i ≥ 0 there exists j ≥ i such that σ[j…] ⊨ φ

**Proof.**

By part 1, σ ⊨ □◇φ iff for all i ≥ 0: σ[i…] ⊨ ◇φ.

By the semantics of ◇: σ[i…] ⊨ ◇φ iff there exists k ≥ 0 such that (σ[i…])[k…] ⊨ φ.

Now, (σ[i…])[k…] = σ[(i+k)…]. Setting j = i + k, we have j ≥ i (since k ≥ 0).

So: σ[i…] ⊨ ◇φ iff there exists j ≥ i such that σ[j…] ⊨ φ.

Combining: σ ⊨ □◇φ iff for all i ≥ 0, there exists j ≥ i such that σ[j…] ⊨ φ.

This is exactly the characterization of "φ holds infinitely often": no matter how far along the sequence we are (at position i), we can always find a future position j where φ holds. ∎


---

## Exercise 2: LTL properties of transition systems

**The transition system T:**
- States: S = {s₁, s₂, s₃}
- Initial state: I = {s₁}
- Transitions: s₁→s₁, s₁→s₂, s₂→s₃, s₃→s₃, s₃→s₂
- Labels: λ(s₁) = {p, q}, λ(s₂) = {p, q}, λ(s₃) = {p}

Recall: T ⊨ φ iff for ALL maximal paths starting from ALL initial states, the trace satisfies φ.

Since s₁ is the only initial state, we need every infinite path from s₁ to satisfy φ.


### 1. □p — "p holds always"

**T ⊨ □p. TRUE.**

In every state, p holds: λ(s₁) = {p,q}, λ(s₂) = {p,q}, λ(s₃) = {p}. So p ∈ λ(s) for all s ∈ S. Every trace has p true at every position, so σ[j…] ⊨ p for all j ≥ 0, giving σ ⊨ □p.


### 2. ○(p ∧ q) — "in the next state, p and q both hold"

**T ⊨ ○(p ∧ q). FALSE.**

Consider the path ρ = s₁ → s₂ → s₃ → s₃ → …

The trace is: {p,q}, {p,q}, {p}, {p}, …

At position 0 we evaluate ○(p ∧ q): we need p ∧ q to hold at position 1. At position 1 the label is {p,q}, so p ∧ q holds. This path is fine.

But consider the path ρ' = s₁ → s₁ → s₂ → s₃ → s₃ → …

At position 1 we have {p,q} — still fine.

Actually, from s₁ the successors are s₁ and s₂. Both have label {p,q}, so p ∧ q holds in the next state for any path starting at s₁.

Wait — let me reconsider. T ⊨ ○(p ∧ q) requires that for ALL paths from s₁, position 1 satisfies p ∧ q.

From s₁, we can go to s₁ (label {p,q}) or s₂ (label {p,q}). Both satisfy p ∧ q.

**T ⊨ ○(p ∧ q). TRUE.**


### 3. □(¬q → □(p ∧ ¬q)) — "once q becomes false, p ∧ ¬q holds forever after"

**T ⊨ □(¬q → □(p ∧ ¬q)). FALSE.**

Consider the path ρ = s₁ → s₂ → s₃ → s₂ → s₃ → s₂ → …

The trace is: {p,q}, {p,q}, {p}, {p,q}, {p}, {p,q}, …

At position 2 (state s₃), we have ¬q (since λ(s₃) = {p}). The formula requires that □(p ∧ ¬q) holds from position 2 onward. But at position 3 (state s₂), q holds, so p ∧ ¬q is false. Therefore □(p ∧ ¬q) fails.

This path violates the property: after entering a ¬q state, the system can return to a q state (via s₃→s₂).


### 4. q U (p ∧ ¬q) — "q holds until we reach a state where p ∧ ¬q"

**T ⊨ q U (p ∧ ¬q). FALSE.**

Consider the path ρ = s₁ → s₁ → s₁ → s₁ → … (staying in s₁ forever).

The trace is: {p,q}, {p,q}, {p,q}, …

For q U (p ∧ ¬q), there must exist some j ≥ 0 where σ[j…] ⊨ p ∧ ¬q. But at every position, q is true (since we stay in s₁), so p ∧ ¬q is never satisfied. The "until" requires the right-hand side to eventually hold, which it never does on this path.
