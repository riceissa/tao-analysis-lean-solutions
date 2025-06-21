import Mathlib.Tactic

/-!
# Analysis I, Section 9.2

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Recalling basic pointwise operations on functions

-/

namespace Chapter9

open Classical in
noncomputable abbrev function_example : ℝ → ℝ := fun x ↦ if x ∈ ((fun y:ℚ ↦ (y:ℝ)) '' Set.univ) then 1 else 0

/-- Definition 9.2.1 (Arithmetic operations on functions)-/
theorem add_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f + g) x = f x + g x := by
  rfl

theorem sub_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f - g) x = f x - g x := by
  rfl

theorem max_func_eval (f g: ℝ → ℝ) (x: ℝ) : max f g x = max (f x) (g x) := by
  rfl

theorem min_func_eval (f g: ℝ → ℝ) (x: ℝ) : min f g x = min (f x) (g x) := by
  rfl

theorem mul_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f * g) x = f x * g x := by
  rfl

theorem div_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f / g) x = f x / g x := by
  rfl

theorem smul_func_eval (c: ℝ) (f: ℝ → ℝ) (x: ℝ) : (c • f) x = c * f x := by
  rfl

abbrev f_9_2_2 : ℝ → ℝ := fun x ↦ x^2

abbrev g_9_2_2 : ℝ → ℝ := fun x ↦ 2*x

example : f_9_2_2 + g_9_2_2 = fun x ↦ x^2 + 2*x := by
  rfl

example : f_9_2_2 * g_9_2_2 = fun x ↦ 2 * x^3 := by ext x; simp; ring

example : f_9_2_2 - g_9_2_2 = fun x ↦ x^2 - 2*x := by
  rfl

example : 6 • f_9_2_2 = fun x ↦ 6 * (x^2) := by ext x; simp

example : f_9_2_2 ∘ g_9_2_2 = fun x ↦ 4*x^2 := by ext x; simp; ring

example : g_9_2_2 ∘ f_9_2_2 = fun x ↦ 2*x^2 := by ext x; simp

/- Exercise 9.2.1.  For each of the pairs below, uncomment and prove one of the claims, and disprove the other.-/

--example : ∀ (f g h : ℝ → ℝ), (f+g) ∘ h = f ∘ h + g ∘ h := by sorry
--example : ¬ ∀(f g h : ℝ → ℝ), (f+g) ∘ h = f ∘ h + g ∘ h := by sorry

--example : ∀ (f g h : ℝ → ℝ), f ∘ (g + h) = f ∘ g + f ∘ h := by sorry
--example : ¬ ∀(f g h : ℝ → ℝ), f ∘ (g + h) = f ∘ g + f ∘ h := by sorry

--example : ∀ (f g h : ℝ → ℝ), (f+g) * h = f * h + g * h := by sorry
--example : ¬ ∀(f g h : ℝ → ℝ), (f+g) * h = f * h + g * h := by sorry

--example : ∀ (f g h : ℝ → ℝ), f * (g+h) = f * g + f * h := by sorry
--example : ¬ ∀(f g h : ℝ → ℝ), f * (g+h) = f * g + f * h := by sorry


end Chapter9
