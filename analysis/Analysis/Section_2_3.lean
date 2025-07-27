import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the `*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's `Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's `Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's `Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's `Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  -- This formalization is based on the proof at https://taoanalysis.wordpress.com/2020/04/02/exercise-2-3-1/
  revert n; apply induction
  . rw [Nat.zero_mul]
  . intro n hind
    rw [Nat.succ_mul, hind, Nat.zero_add]

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's `Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  -- This formalization is based on the proof at https://taoanalysis.wordpress.com/2020/04/02/exercise-2-3-1/
  revert n; apply induction
  . rw [Nat.zero_mul]
    rw [Nat.zero_mul, Nat.zero_add]
  . intro n hind
    rw [Nat.succ_mul]
    rw [hind]
    rw [Nat.succ_mul]
    rw [Nat.add_assoc, Nat.add_succ, Nat.add_comm n m]
    rw [Nat.add_assoc, Nat.add_succ m n]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's `Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  -- This formalization is based on the proof at https://taoanalysis.wordpress.com/2020/04/02/exercise-2-3-1/
  revert n; apply induction
  . rw [Nat.zero_mul, Nat.mul_zero]
  . intro n hind
    rw [Nat.succ_mul, Nat.mul_succ]
    rw [hind]

/-- Compare with Mathlib's `Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]



/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's `Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  -- This formalization is based on the model solution at https://taoanalysis.wordpress.com/2020/04/03/exercise-2-3-2/
  constructor
  . contrapose!
    intro h
    rw [← isPos_iff, ← isPos_iff] at h
    obtain ⟨ hn, hm ⟩ := h
    apply Nat.succ_eq at hn
    apply Nat.succ_eq at hm
    obtain ⟨ a, ha ⟩ := hn
    obtain ⟨ b, hb ⟩ := hm
    rw [← ha, ← hb]
    rw [Nat.succ_mul, Nat.mul_succ]
    rw [Nat.add_succ]
    apply Nat.succ_ne
  . intro h
    obtain hn|hm := h
    rw [hn, Nat.zero_mul]
    rw [hm, Nat.mul_zero]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's `Nat.mul_pos`

Note from Issa: I actually ended up doing the reverse, of proving mul_eq_zero directly and then proving the following as a special case. But I might want to swap the two back to how it is in the main repo. -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  have h := Nat.mul_eq_zero
  specialize h n m
  tauto

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's `Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  -- This is a formalization of the model solution at https://taoanalysis.wordpress.com/2020/04/04/exercise-2-3-3/
  revert a; apply induction
  . rw [Nat.zero_mul, Nat.zero_mul]
    rw [Nat.zero_mul]
  . intro a hind
    rw [Nat.succ_mul, Nat.add_mul, hind, ← Nat.succ_mul]

/-- (Not from textbook)  Nat is a commutative semiring.
    This allows tactics such as `ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the `ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's `Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's `Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's `Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

lemma Nat.mul_le_mul_of_nonneg_left' {a b c : Nat} (hab : a ≤ b) : c * a ≤ c * b := by
  rw [le_iff] at hab
  obtain ⟨ d, hd ⟩ := hab
  use (c*d)
  rw [hd]
  rw [Nat.mul_add]

/-- (Not from textbook) Nat is an ordered semiring.
This allows tactics such as `gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by
    use 1
    rw [zero_add]
  mul_le_mul_of_nonneg_left := by
    intro a b c
    intro h1 h2
    exact Nat.mul_le_mul_of_nonneg_left' h1
  mul_le_mul_of_nonneg_right := by
    intro a b c
    rw [mul_comm a c, mul_comm b c]
    intro hab hc
    exact Nat.mul_le_mul_of_nonneg_left' hab

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's `Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  . use 0
    use 0
    constructor
    . tauto
    . constructor
      . rw [isPos_iff_gt_zero] at hq
        rw [Nat.gt_iff_lt] at hq
        exact hq
      . rw [zero_mul, add_zero]
  intro n h
  obtain ⟨ m, hm ⟩ := h
  obtain ⟨ r, hr ⟩ := hm
  obtain ⟨ h1, h2 ⟩ := hr
  obtain ⟨ h2, h3 ⟩ := h2
  apply_fun (· + 1) at h3
  rw [lt_iff_succ_le] at h2
  rw [Nat.le_iff_lt_or_eq] at h2
  rcases h2 with hlt | heq
  . use m
    use (r++)
    constructor
    rw [← Nat.ge_iff_le]
    exact ge_zero (r++)
    constructor
    exact hlt
    rw [add_one, add_one, ← add_succ] at h3
    exact h3
  . rw [add_assoc] at h3
    rw [add_one r] at h3
    rw [heq] at h3
    use (m + 1)
    use 0
    constructor
    tauto
    constructor
    rw [← heq]
    rw [← gt_iff_lt]
    exact succ_gt_zero r
    rw [← add_one]
    rw [add_mul]
    rw [one_mul, add_zero]
    exact h3

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's `Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  -- rw [←zero_succ, pow_succ]; simp -- this one-liner is from the main repo
  rw [← zero_succ]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

lemma Nat.self_mul_is_squared (m : Nat) : m * m = m ^ (2:Nat) := by
  nth_rewrite 2 [← pow_one m]
  rw [mul_comm]
  rw [← pow_succ]
  rw [one_succ]

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  -- This proof was written to emulate https://taoanalysis.wordpress.com/2020/03/15/exercise-2-3-4/
  rw [← self_mul_is_squared]
  rw [mul_add, add_mul]
  rw [self_mul_is_squared]
  rw [mul_comm b a]
  rw [add_mul]
  rw [self_mul_is_squared]
  -- NOTE(issa 2025-06-26): The ring tactic is a little too powerful for my taste, but doing all the add_assoc to rearrange things just right is too annoying, so I will leave it like this for now...
  ring

end Chapter2
