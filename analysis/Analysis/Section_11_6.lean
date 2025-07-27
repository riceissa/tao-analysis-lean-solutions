import Mathlib.Tactic
import Analysis.Section_9_8
import Analysis.Section_11_5

/-!
# Analysis I, Section 11.6: Riemann integrability of monotone functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions.

-/

namespace Chapter11
open Chapter9 BoundedInterval

/-- Proposition 11.6.1 -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    aesop
  have hbound :=  BddOn.of_monotone hf
  set I := Icc a b
  have hab' : a ≤ b := by linarith
  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    obtain ⟨ N, hN ⟩ := exists_nat_gt (1/ε)
    have hNpos : 0 < N := by
      rify
      have : 0 < 1/ε := by positivity
      linarith
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    have hbeq : b = a + δ*N := by simp [δ]; field_simp
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' j k hjk := by
        simp at hjk
        rcases hjk with hjk | hjk <;> linarith
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (Finset.map e (Finset.range N))
      exists_unique := by
        intro x hx; simp
        by_cases hb: x = b
        . apply ExistsUnique.intro (Icc b b)
          . simp [hb, mem_iff]
          rintro J ⟨ hJ | ⟨ j, hA, hej ⟩, hJb ⟩
          . exact hJ
          simp [←hej, e, mem_iff, hb, hbeq] at hJb
          replace hJb := hJb.2
          rw [mul_lt_mul_iff_of_pos_left hδpos] at hJb
          norm_cast at hJb; linarith
        simp [I, mem_iff] at hx
        set j := ⌊ (x-a)/δ ⌋₊
        have hxa : 0 ≤ x-a := by linarith
        have hxaδ : 0 ≤ (x-a)/δ := by positivity
        have hxb : x < b := by contrapose! hb; linarith
        have hxj : x ∈ e j := by
          simp [e, mem_iff, j]
          constructor
          . calc
              _ ≤ a + δ * ((x-a)/δ) := by gcongr; exact Nat.floor_le hxaδ
              _ = x := by field_simp
          calc
            _ = a + δ * ((x-a)/δ) := by field_simp
            _ < _ := by gcongr; exact Nat.lt_floor_add_one _
        apply ExistsUnique.intro (e j)
        . refine ⟨ ?_, hxj ⟩
          right; use j
          simp [j, Nat.floor_lt hxaδ, div_lt_iff₀' hδpos]
          linarith
        rintro J ⟨ hJ | ⟨ k, hk, hkx ⟩, hxJ ⟩
        . simp [hJ, mem_iff] at hxJ; linarith
        simp [←hkx, mem_iff, e] at hxJ hxj
        rcases lt_trichotomy j k with hjk | hjk | hjk
        . replace hjk : δ*((j:ℝ)+1) ≤ δ*(k:ℝ) := by
            rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
          linarith
        . rw [hjk,hkx]
        replace hjk : δ*((k:ℝ)+1) ≤ δ*(j:ℝ) := by
          rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
        linarith
      contains J hJ := by
        simp at hJ
        rcases hJ with rfl | ⟨ j, hj, rfl ⟩ <;> simp [subset_iff, e, I]
        . linarith
        apply Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc _ _)
        . simp; positivity
        simp [hbeq]; gcongr; norm_cast
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ Finset.range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≤ ∑ j ∈ Finset.range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum
        intro j hj
        convert (mul_le_mul_right hδpos).mpr ?_
        . simp [length]; ring_nf
          simp [le_of_lt hδpos]
        apply csSup_le
        . simp; ring_nf; linarith
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; simp at hj; linarith
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ (le_of_lt hx2) <;> simp [I, hδj1, this]
        exact ⟨ by linarith, by linarith ⟩
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ :=
        lower_integ_ge_lower_sum hbound P
      _ = ∑ j ∈ Finset.range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≥ ∑ j ∈ Finset.range N, f (a + δ*j) * δ := by
        apply Finset.sum_le_sum
        intro j hj
        convert (mul_le_mul_right hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply le_csInf
        . simp; ring_nf; linarith
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have hajb': a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; simp at hj; linarith
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ hx1
        . simp [I]; exact ⟨ by linarith, by linarith ⟩
        simp [I, hδj]; exact ⟨ by linarith, by linarith ⟩
    calc
      _ ≤ ∑ j ∈ Finset.range N, f (a + δ*(j+1)) * δ - ∑ j ∈ Finset.range N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        rw [←Finset.sum_sub_distrib]
        have := Finset.sum_range_sub (fun n ↦ f (a + δ*n) * δ) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        convert this using 1
        simp [hbeq]; ring
      _ ≤ _ := by
        have : 0 ≤ f b - f a := by
          simp; apply hf (by simp [I, hab']) (by simp [I, hab']); exact hab'
        simp [mul_assoc, δ]; gcongr
        rw [div_le_iff₀' (by positivity), mul_comm, mul_assoc]
        nth_rewrite 1 [←mul_one (b-a)]
        gcongr
        rw [←div_le_iff₀' (by positivity)]; linarith
  refine ⟨ hbound, ?_ ⟩
  replace := nonneg_of_le_const_mul_eps this
  have low_le_up : lower_integral f I ≤ upper_integral f I := lower_integral_le_upper hbound
  linarith


/-- Proposition 11.6.1 -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  rw [←neg_neg f]
  apply (integ_of_neg _).1
  apply integ_of_monotone
  convert hf.neg using 1

/-- Corollary 11.6.3 / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  sorry

theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  sorry

/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (Set.Ici 0)) :
  Summable f ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.

/-- Exercise 11.6.4 -/
example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), Summable f ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

example : ∃ (f:ℝ → ℝ) (hnon: ∀ x ≥ 0, f x ≥ 0), ¬ Summable f ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  sorry

end Chapter11
