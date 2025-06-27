import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Analysis I, Section 10.1

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's `HasDerivWithinAt`, `derivWithin`, and `DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that
differentiability is defined even at points that are not limit points of the domain;
derivatives in such cases may not be unique, but `derivWithin` still selects one such
derivative in such cases (or `0`, if no derivative exists).

-/

namespace Chapter10

/-- Definition 10.1.1 (Differentiability at a point).  For the Mathlib notion `HasDerivWithinAt`, the
hypothesis that `x₀` is a limit point is not needed. -/
theorem _root_.HasDerivWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ)
  (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔ Filter.Tendsto (fun x ↦ (f x - f x₀) / (x - x₀))
  (nhds x₀ ⊓ Filter.principal (X \ {x₀})) (nhds L) :=  by
  rw [hasDerivWithinAt_iff_tendsto_slope, ←nhdsWithin.eq_1, iff_iff_eq, slope_fun_def_field]

theorem _root_.DifferentiableWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ) :
  DifferentiableWithinAt ℝ f X x₀ ↔ ∃ L, HasDerivWithinAt f L X x₀ := by
  constructor
  . intro h
    use derivWithin f X x₀
    exact DifferentiableWithinAt.hasDerivWithinAt h
  rintro ⟨ L, h ⟩
  exact HasDerivWithinAt.differentiableWithinAt h

theorem _root_.DifferentiableWithinAt.of_hasDeriv {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ} {L:ℝ}
  (hL: HasDerivWithinAt f L X x₀) : DifferentiableWithinAt ℝ f X x₀ := by
  rw [DifferentiableWithinAt.iff]; use L


theorem derivative_unique {X: Set ℝ} {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (Filter.principal (X \ {x₀}))) {f: ℝ → ℝ} {L L':ℝ}
  (hL: HasDerivWithinAt f L X x₀) (hL': HasDerivWithinAt f L' X x₀) :
  L = L' := by
    rw [_root_.HasDerivWithinAt.iff] at hL hL'
    rw [ClusterPt.eq_1] at hx₀
    apply tendsto_nhds_unique hL hL'

#check DifferentiableWithinAt.hasDerivWithinAt

theorem derivative_unique' (X: Set ℝ) {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (Filter.principal (X \ {x₀}))) {f: ℝ → ℝ} {L :ℝ}
  (hL: HasDerivWithinAt f L X x₀)
  (hdiff : DifferentiableWithinAt ℝ f X x₀):
  L = derivWithin f X x₀ :=
  derivative_unique hx₀ hL (DifferentiableWithinAt.hasDerivWithinAt hdiff)


/-- Example 10.1.3 -/
example (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) (Set.univ) x₀ := by
  sorry

example (x₀:ℝ) : DifferentiableWithinAt ℝ (fun x ↦ x^2) (Set.univ) x₀ := by
  sorry

example (x₀:ℝ) : derivWithin (fun x ↦ x^2) (Set.univ) x₀ = 2 * x₀ := by
  sorry

/-- Remark 10.1.4 -/
example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (hfg: f = g):
  DifferentiableWithinAt ℝ f X x₀ ↔ DifferentiableWithinAt ℝ g X x₀ := by rw [hfg]


example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (L:ℝ) (hfg: f = g):
  HasDerivWithinAt f L X x₀ ↔ HasDerivWithinAt g L X x₀ := by rw [hfg]

example : ∃ (X: Set ℝ) (x₀ :ℝ) (f g: ℝ → ℝ) (L:ℝ) (hfg: f x₀ = g x₀),
  HasDerivWithinAt f L X x₀ ∧ ¬ HasDerivWithinAt g L X x₀ := by
  sorry

/-- Example 10.1.6 -/

abbrev f_10_1_6 : ℝ → ℝ := abs

example : Filter.Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
  (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) (nhds 1) := by
  sorry

example : Filter.Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
  (nhds 0 ⊓ Filter.principal (Set.Iio 0)) (nhds (-1)) := by
  sorry

example : ¬ ∃ L, Filter.Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
  (nhds 0 ⊓ Filter.principal (Set.univ \ {0})) (nhds L) := by sorry

example : ¬ DifferentiableWithinAt ℝ f_10_1_6 (Set.univ) 0 := by
  sorry

example : DifferentiableWithinAt ℝ f_10_1_6 (Set.Ioi 0) 0 := by
  sorry

example : derivWithin f_10_1_6 (Set.Ioi 0) 0 = 1 := by
  sorry

example : DifferentiableWithinAt ℝ f_10_1_6 (Set.Iio 0) 0 := by
  sorry

example : derivWithin f_10_1_6 (Set.Iio 0) 0 = -1 := by
  sorry

/-- Proposition 10.1.7 (Newton's approximation) / Exercise 10.1.2 -/
theorem _root_.HasDerivWithinAt.iff_approx_linear (X: Set ℝ) (x₀ :ℝ) (f: ℝ → ℝ) (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → |f x - f x₀ - L * (x - x₀)| ≤ ε * |x - x₀| := by
  sorry

/-- Proposition 10.0.1 / Exercise 10.1.3 -/
theorem _root_.ContinuousWithinAt.of_differentiableWithinAt {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ}
  (h: DifferentiableWithinAt ℝ f X x₀) :
  ContinuousWithinAt f X x₀ := by
  sorry

/-Definition 10.1.11 (Differentiability on a domain)-/
#check DifferentiableOn.eq_1

/-- Corollary 10.1.12 -/
theorem _root_.ContinuousOn.of_differentiableOn {X: Set ℝ} {f: ℝ → ℝ}
  (h: DifferentiableOn ℝ f X) :
  ContinuousOn f X := by
  intro x hx
  have hdiff := h x hx
  exact ContinuousWithinAt.of_differentiableWithinAt hdiff

/-- Theorem 10.1.13 (a) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_const (X: Set ℝ) (x₀ : ℝ) (c:ℝ) :
  HasDerivWithinAt (fun x ↦ c) 0 X x₀ := by sorry

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by sorry

/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (f) (Difference rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_sub {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f - g) (f'x₀ - g'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (g) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_inv {X: Set ℝ} {x₀ g'x₀: ℝ}
  {g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (1/g) (-g'x₀ / (g x₀)^2) X x₀ := by
  sorry

/-- Theorem 10.1.13 (h) (Quotient rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_div {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f / g) ((f'x₀ * (g x₀) - (f x₀) * g'x₀) / (g x₀)^2) X x₀ := by
  sorry

example (x₀:ℝ) (hx₀: x₀ ≠ 1): HasDerivWithinAt (fun x ↦ (x-2)/(x-1)) (1 /(x₀-1)^2) (Set.univ \ {1}) x₀ := by
  sorry

/-- Theorem 10.1.15 (Chain rule) / Exercise 10.1.7 -/
theorem _root_.HasDerivWithinAt.of_comp {X Y: Set ℝ} {x₀ y₀ f'x₀ g'y₀: ℝ}
  {f g: ℝ → ℝ} (hfx₀: f x₀ = y₀) (hfX : ∀ x ∈ X, f x ∈ Y)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  HasDerivWithinAt (g ∘ f) (g'y₀ * f'x₀) X x₀ := by
  sorry

/-- Exercise 10.1.5 -/
theorem _root_.HasDerivWithinAt.of_pow (n:ℕ) (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^n)
(n * x₀^((n:ℤ)-1)) (Set.univ) x₀ := by
  sorry

/-- Exercise 10.1.6 -/
theorem _root_.HasDerivWithinAt.of_zpow (n:ℤ) (x₀:ℝ) (hx₀: x₀ ≠ 0) :
  HasDerivWithinAt (fun x ↦ x^n) (n * x₀^(n-1)) (Set.univ \ {0}) x₀ := by
  sorry



end Chapter10
