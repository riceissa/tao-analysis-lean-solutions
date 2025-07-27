import Mathlib.Tactic
import Mathlib.Topology.ContinuousOn
import Analysis.Section_7_3
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_11_6
import Analysis.Section_11_8


/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/

namespace Chapter11
open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus)-/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (Set.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  obtain ⟨ M, hM ⟩ := hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := (integ_of_join (join_Icc_Ioc hy.1 hy.2) hf).1
    replace := (integ_of_join (join_Icc_Ioc hx.1 (le_of_lt hxy)) this).2
    simp [F, this.2, abs_le']
    constructor
    . convert integ_mono (g := fun _ ↦ M) this.1 (integ_of_const _ _).1 _
      . simp [integ_of_const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at hz ⊢
        exact ⟨ by linarith, by linarith ⟩
      rw [abs_le'] at hM; simp [hM]
    rw [neg_le]
    convert integ_mono (f := fun _ ↦ -M) (integ_of_const _ _).1 this.1 _
    . simp [integ_of_const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at hz ⊢
      exact ⟨ by linarith, by linarith ⟩
    rw [abs_le'] at hM; simp; linarith
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    rcases lt_trichotomy x y with h | h | h
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp [h]
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (Set.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; exact le_max_left _ _
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (Set.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  intro ε hε
  simp [(ContinuousWithinAt.tfae _ f hx₀).out 0 2] at hcts
  specialize hcts ε hε
  obtain ⟨ δ, hδ, hconv ⟩ := hcts; use δ, hδ; intro y hy hyδ
  rcases lt_trichotomy x₀ y with hx₀y | hx₀y | hx₀y
  . have := (integ_of_join (join_Icc_Ioc hy.1 hy.2) hf).1
    replace := (integ_of_join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y)) this).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := integ_mono (g := fun _ ↦ f x₀ + ε) this.1 (integ_of_const _ _).1 ?_
    have h2 := integ_mono (f := fun _ ↦ f x₀ - ε) (integ_of_const _ _).1 this.1 ?_
    simp [integ_of_const, le_of_lt hx₀y, BoundedInterval.a, BoundedInterval.b] at h1 h2
    constructor
    . convert h1 using 1; ring
    . simp [←sub_nonneg] at h2 ⊢
      convert h2 using 1; ring
    . intro z hz
      simp at hz hy hx₀
      simp_rw [abs_lt] at hyδ hconv
      specialize hconv z (by linarith) (by linarith) ⟨ by linarith, by linarith ⟩
      simp; linarith
    intro z hz
    simp at hz hy hx₀
    simp_rw [abs_lt] at hyδ hconv
    specialize hconv z (by linarith) (by linarith) ⟨ by linarith, by linarith ⟩
    simp; linarith
  . simp [hx₀y]
  sorry

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) := by
  apply integ_of_monotone
  apply StrictMonoOn.monotoneOn
  exact StrictMonoOn.mono StrictMonoOn.of_f_9_8_5 (by simp)

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (Set.Icc 0 1) := by
  apply cts_of_integ
  exact IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (Set.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) IntegrableOn.of_f_9_8_5 hx'
     (ContinuousAt.continuousWithinAt (ContinuousAt.of_f_9_8_5 hx))
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  use (ContinuousLinearMap.smulRight (1:ℝ →L[ℝ] ℝ) (f_9_8_5 x))

/-- Exercise 11.9.1 -/
theorem DifferentiableOn.of_F_11_9_2' {q:ℚ} (hq: (q:ℝ) ∈ Set.Icc 0 1) : ¬ DifferentiableWithinAt ℝ F_11_9_2 (Set.Icc 0 1) q := by sorry

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

theorem AntiderivOn.mono {F f: ℝ → ℝ} {I J: BoundedInterval}
  (h: AntiderivOn F f I) (hIJ: J ⊆ I) : AntiderivOn F f J := by
  refine ⟨ DifferentiableOn.mono h.1 hIJ, ?_ ⟩
  intro x hx
  rw [subset_iff] at hIJ
  exact HasDerivWithinAt.mono (h.2 x (hIJ hx)) hIJ

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antideriv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by

  -- This proof is written to follow the structure of the original text.
  rcases lt_or_eq_of_le h with h | h
  . have hF_cts : ContinuousOn F (Set.Icc a b) := by
      intro x hx
      exact ContinuousWithinAt.of_differentiableWithinAt (hF.1 x hx)
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦ F (max (min x b) a)

    have hFF' {x:ℝ} (hx: x ∈ Set.Icc a b) : F' x = F x := by
      simp at hx
      simp [F', hx.2, hx.1]

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      apply Continuous.continuousOn
      convert ContinuousOn.comp_continuous hF_cts (f := fun x ↦ max (min x b) a) ?_ ?_ using 1
      . fun_prop
      intro x; simp [le_of_lt h]

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := Partition.sum_of_α_length P F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          rcases le_or_gt J.b J.a with hJab | hJab
          . push_neg at hJ_empty
            obtain ⟨ x, hx ⟩ := hJ_empty
            cases J with
            | Ioo c d => simp at hx; linarith
            | Ioc c d => simp at hx; linarith
            | Ico c d => simp at hx; linarith
            | Icc c d =>
              simp at hx
              have : c = d := by linarith
              simp [this]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                replace hJ := P.contains _ hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          replace hJ := P.contains _ hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by
            apply Set.Icc_subset_Ioo <;> linarith
          replace hJ' := ((Ioo_subset J).trans hJ).trans hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by
            apply Set.Icc_subset_Ioo <;> linarith
          replace hJ'' := hJ.trans hJ''
          rw [α_length_of_cts (by linarith) (le_of_lt hJab) (by linarith) hJ'' hF'_cts]
          have := HasDerivWithinAt.mean_value hJab (ContinuousOn.mono hF'_cts ?_) ?_
          . obtain ⟨ e, he, hmean ⟩ := this
            have : HasDerivWithinAt F' (f e) (Set.Ioo c d) e := by
              replace hJ := (Ioo_subset J).trans hJ
              simp [subset_iff] at hJ
              apply HasDerivWithinAt.congr (f := F)
              . exact HasDerivWithinAt.mono (hF.2 e (hJ he)) hJ
              . intros; solve_by_elim
              solve_by_elim
            replace := derivative_unique ?_ this hmean
            . calc
                _ = F' d - F' c := rfl
                _ = (d - c) * f e := by
                  rw [this]
                  have : d-c > 0 := by linarith
                  field_simp
                _ = f e * |J|ₗ := by
                  simp [mul_comm, length]
                  left; rw [max_eq_left (by linarith)]
                _ ≤ _ := by
                  gcongr
                  apply le_csSup
                  . rw [bddAbove_def]
                    obtain ⟨ M, hM ⟩ := hf.1
                    use M
                    simp only [abs_le', and_imp, Set.mem_image, forall_exists_index,
                      forall_apply_eq_imp_iff₂, F'] at hM ⊢
                    intro x hx
                    rw [subset_iff] at hJ
                    specialize hM x (hJ hx); tauto
                  simp; use e; simp
                  exact ((subset_iff _ _).mp (Ioo_subset J)) he
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := Set.Ioo e d)
            . intro x hx; simp at he hx ⊢
              exact ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩
            simp at he
            rw [closure_Ioo (by linarith)]
            simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]
            exact ⟨ by linarith, by linarith ⟩
          apply DifferentiableOn.congr (f := F)
          . apply DifferentiableOn.mono hF.1
            replace hJ := (Ioo_subset J).trans hJ
            simpa [subset_iff] using hJ
          intro x hx
          have : x ∈ Set.Icc a b := by
            replace hJ := (Ioo_subset J).trans hJ _ hx
            simpa using hJ
          simp only [ite_eq_left_iff, F']; tauto
        _ = F'[Icc a b]ₗ := Partition.sum_of_α_length P F'
        _ = F' b - F' a := by
          apply α_length_of_cts (by linarith) _ (by linarith) _ hF'_cts
          . simp [le_of_lt h]
          intro x hx; simp [mem_iff] at hx ⊢; exact ⟨ by linarith, by linarith ⟩
        _ = _ := by
          congr 1 <;> apply hFF' <;> simp [le_of_lt h]
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      sorry
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]
      apply le_csInf <;> simp [Set.range_nonempty]
      intro P; specialize hupper P; linarith
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]
      apply csSup_le <;> simp [Set.range_nonempty]
      intro P; specialize hlower P; linarith
    replace hf := hf.2
    linarith
  simp [h]
  apply (integ_on_subsingleton _).2
  simp [length]

open Real

noncomputable abbrev F_11_9 : ℝ → ℝ := fun x ↦ if x = 0 then 0 else x^2 * sin (1 / x^3)

example : Differentiable ℝ F_11_9 := by sorry

example : ¬ BddOn (deriv F_11_9) (Set.Icc (-1) 1) := by sorry

example : AntiderivOn F_11_9 (deriv F_11_9) (Icc (-1) 1) := by sorry

/-- Lemma 11.9.5 / Exercise 11.9.2 -/
theorem antideriv_eq_antideriv_add_const {I:BoundedInterval} {f F G : ℝ → ℝ}
  (hfF: AntiderivOn F f I) (hfG: AntiderivOn G f I) :
   ∃ C, ∀ x ∈ (I:Set ℝ), F x = G x + C := by
    sorry

/-- Exercise 11.9.3 -/
example {a b x₀:ℝ} (hab: a < b) (hx₀: x₀ ∈ Icc a b) {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
  ContinuousWithinAt f (Icc a b) x₀ := by
  sorry

end Chapter11

/-- Exercise 11.6.5, moved to Section 11.9 -/
theorem Chapter7.Series.converges_qseries' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).converges ↔ (p>1) := by
  sorry

theorem Chapter7.Series.converges_qseries'' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).absConverges ↔ (p>1) := by
  sorry
