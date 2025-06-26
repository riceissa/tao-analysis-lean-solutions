import Mathlib.Tactic
import Analysis.Section_9_6

/-!
# Analysis I, Section 10.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives
- Rolle's theorem
- mean value theorem

-/

open Chapter9
namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's `IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff ]
  apply exists_congr; intro ε
  apply and_congr_right; intro hε
  apply forall_congr'; intro x
  constructor
  . intro h hx hxm hxp
    exact h (by linarith) (by linarith) hx
  intro h hxm hxp hx
  exact h hx (by linarith) (by linarith)

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff ]
  apply exists_congr; intro ε
  apply and_congr_right; intro hε
  apply forall_congr'; intro x
  constructor
  . intro h hx hxm hxp
    exact h (by linarith) (by linarith) hx
  intro h hxm hxp hx
  exact h hx (by linarith) (by linarith)

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

example : ¬ IsMinOn f_10_2_3 Set.univ 0 := by sorry

example : IsMinOn f_10_2_3 (Set.Ioo (-1) 1) 0 := by sorry

example : IsLocalMaxOn f_10_2_3 Set.univ 0 := by sorry

/-- Example 10.2.4 -/
example : ¬ ∃ x, IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' Set.univ) x := by sorry

example : ¬ ∃ x, IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' Set.univ) x := by sorry

example (n:ℤ) : IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' Set.univ) n := by sorry

example (n:ℤ) : IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' Set.univ) n := by sorry

/-- Remark 10.2.5 -/
theorem IsLocalMaxOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMaxOn f X x₀) : IsLocalMaxOn f Y x₀ := by
  sorry

theorem IsLocalMinOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMinOn f X x₀) : IsLocalMinOn f Y x₀ := by
  sorry

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMaxOn.deriv_eq_zero {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMaxOn f (Set.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (Set.Ioo a b) x₀) : L = 0 := by
  sorry

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMinOn.deriv_eq_zero {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMinOn f (Set.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (Set.Ioo a b) x₀) : L = 0 := by
  sorry

theorem IsMaxOn.deriv_eq_zero_counter : ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ)
  (x₀:ℝ) (hx₀: x₀ ∈ Set.Icc a b) (h: IsMaxOn f (Set.Icc a b) x₀) (L:ℝ)
  (hderiv: HasDerivWithinAt f L (Set.Icc a b) x₀), L ≠ 0 := by
  sorry

/-- Theorem 10.2.7 (Rolle's theorem) / Exercise 10.2.4 -/
theorem HasDerivWithinAt.exist_zero {a b:ℝ} (hab: a < b) {g:ℝ → ℝ}
  (hcont: ContinuousOn g (Set.Icc a b)) (hderiv: DifferentiableOn ℝ g (Set.Ioo a b))
  (hgab: g a = g b) : ∃ x ∈ Set.Ioo a b, HasDerivWithinAt g 0 (Set.Ioo a b) x := by
  sorry

/-- Corollary 10.2.9 (Mean value theorem ) / Exercise 10.2.5 -/
theorem HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (Set.Icc a b)) (hderiv: DifferentiableOn ℝ f (Set.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (Set.Ioo a b) x := by
  sorry

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (Set.Icc (-1) 1) ∧
  IsMaxOn f (Set.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (Set.Icc (-1) 1) 0 := by
  sorry

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (Set.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (Set.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (Set.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (Set.Icc (-1) 1) 0 := by
  sorry

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (Set.Icc a b))
  (hderiv: DifferentiableOn ℝ f (Set.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (Set.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  sorry

/-- Exercise 10.2.7 -/
theorem UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f Set.univ)
  (hderiv: DifferentiableOn ℝ f Set.univ)
  (hlip: BddOn (deriv f) Set.univ) :
  UniformContinuousOn f (Set.univ) := by
  sorry


end Chapter10
