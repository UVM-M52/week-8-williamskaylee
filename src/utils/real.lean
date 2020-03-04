
import .cmp

attribute [instance, priority 10] classical.prop_decidable

axiom ℝ : Type

@[instance]
axiom real_field : discrete_linear_ordered_field ℝ

axiom sup (s : ℕ → ℝ) : (∀ n, s n ≤ s (n+1)) → (∃ b, ∀ n, s n ≤ b) → ℝ

axiom sup_spec (s : ℕ → ℝ) (hm : ∀ n, s n ≤ s (n+1)) (hb : ∃ b, ∀ n, s n ≤ b) : (∀ n, s n ≤ sup s hm hb) ∧ (∀ b, (∀ n, s n ≤ b) → sup s hm hb ≤ b)
