import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded
- Continuous functions on closed and bounded intervals attain their maximum and minimum
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop :=
  ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) :
  BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  sorry

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :
  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  sorry

example : Continuous (fun x:ℝ ↦ x) := by sorry

example : ¬ BddOn (fun x:ℝ ↦ x) Set.univ  := by sorry

example : BddOn (fun x:ℝ ↦ x) (Set.Icc 1 2) := by sorry

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 1) := by sorry

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 1) := by sorry

theorem why_7_6_3 {n: ℕ → ℕ} (hn: StrictMono n) (j:ℕ) : n j ≥ j := by sorry

/-- Lemma 7.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b) ) :
  BddOn f (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound
  simp [BddOn] at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := (hunbound n).choose_spec
  set X := Set.Icc a b
  have hXclosed : IsClosed X := Icc_closed (by linarith)
  have hXbounded : Bornology.IsBounded X := Icc_bounded _ _
  have haX (n:ℕ): x n ∈ X := by simp [X]; exact ⟨ (hx n).1, (hx n).2.1 ⟩
  obtain ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := ContinuousOn.continuousWithinAt hf hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := Convergesto.comp (AdherentPt.of_mem hLX) hf (fun j ↦ haX (n j)) hconv
  replace hf := Metric.isBounded_range_of_tendsto _ hf
  rw [isBounded_def] at hf
  obtain ⟨ M, hpos, hM ⟩ := hf
  obtain ⟨ j, hj ⟩ := exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by
    apply hM; simp
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/-- Definition 7.6.5 -/
abbrev HasMaxAt (f:ℝ → ℝ) (X:Set ℝ) (x₀:ℝ) : Prop :=
  ∀ x ∈ X, f x ≤ f x₀

abbrev HasMinAt (f:ℝ → ℝ) (X:Set ℝ) (x₀:ℝ) : Prop :=
  ∀ x ∈ X, f x₀ ≤ f x

/-- Remark 7.6.6 -/
theorem BddAboveOn.hasMaxAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMaxAt f X x₀): BddAboveOn f X := by sorry

theorem BddBelowOn.hasMinAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: HasMinAt f X x₀): BddBelowOn f X := by sorry

/-- Proposition 9.6.7 (Maximum principle) -/
theorem HasMaxAt.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, HasMaxAt f (Set.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  have hbound := BddOn.of_continuous_on_compact h hf
  obtain ⟨ M, hM ⟩ := hbound
  set E := f '' (Set.Icc a b)
  have hE : E ⊆ Set.Icc (-M) M := by
    rintro _ ⟨ x, hx, rfl ⟩
    simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by
    simp [E]
    contrapose! h
    rw [Set.Icc_eq_empty_iff] at h
    linarith
  set m := sSup E
  have claim1 {y:ℝ} (hy: y ∈ E) : y ≤ m :=
    le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  . sorry
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1:ℝ) < f x := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : m - 1/(n+1:ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    replace := exists_lt_of_lt_csSup hnon this
    simp only [Set.mem_image, exists_exists_and_eq_and, E] at this
    exact this
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : m - 1/(n+1:ℝ) < f (x n) := (claim2 n).choose_spec.2
  have hclosed : IsClosed (Set.Icc a b) := Icc_closed (by linarith)
  have hbounded : Bornology.IsBounded (Set.Icc a b) := Icc_bounded _ _
  obtain ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (Set.Icc a b)).mp ⟨ hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.Tendsto (fun j ↦ f (x (n j))) Filter.atTop (nhds (f xmax)) :=
    Filter.Tendsto.comp_of_continuous hmax (hf.continuousWithinAt hmax) (fun j ↦ hx (n j)) hconv
  have hlower (j:ℕ) : m - 1/(j+1:ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j))
    gcongr
    exact hn_lower j
  have hupper (j:ℕ) : f (x (n j)) ≤ m := by
    apply claim1
    simp only [Set.mem_image, E]
    use x (n j), hx (n j)
  have hconvm : Filter.Tendsto (fun j ↦ f (x (n j))) Filter.atTop (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1:ℝ)) (h := fun j ↦ m) (f := fun j ↦ f (x (n j)))
    . convert Filter.Tendsto.const_sub m (c:=0) _
      . simp
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    . exact tendsto_const_nhds
    . intro j; exact le_of_lt (hlower j)
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm






theorem HasMinAt.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (Set.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, HasMinAt f (Set.Icc a b) xmin := by
  sorry

example : HasMaxAt (fun x ↦ x^2) (Set.Icc (-2) 2) 2 := by sorry

example : HasMaxAt (fun x ↦ x^2) (Set.Icc (-2) 2) (-2) := by sorry

theorem sSup.of_hasMaxAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: HasMaxAt f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_hasMinAt {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: HasMinAt f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' Set.Icc a b) = f xmax := by
  obtain ⟨ xmax, hmax, hhas ⟩ := HasMaxAt.of_continuous_on_compact h hf
  exact ⟨ xmax, hmax, sSup.of_hasMaxAt hmax hhas ⟩

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (Set.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' Set.Icc a b) = f xmin := by
  obtain ⟨ xmin, hmin, hhas ⟩ := HasMinAt.of_continuous_on_compact h hf
  exact ⟨ xmin, hmin, sInf.of_hasMinAt hmin hhas ⟩

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (Set.Ioo 1 2) ∧ BddOn f (Set.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, HasMinAt f (Set.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, HasMaxAt f (Set.Ioo 1 2) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (Set.Ioo 1 2) ∧ BddOn f (Set.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, HasMaxAt f (Set.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, HasMinAt f (Set.Ioo 1 2) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, BddOn f (Set.Icc (-1) 1) ∧
  ¬ ∃ x₀ ∈ Set.Icc (-1) 1, HasMinAt f (Set.Icc (-1) 1) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Icc (-1) 1, HasMaxAt f (Set.Icc (-1) 1) x₀
  := by sorry

/-- Exercise 9.6.1 -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (Set.Icc (-1) 1) ∧ ¬ BddBelowOn f (Set.Icc (-1) 1) := by sorry


end Chapter9
