import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  -- This proof was written by Issa.
  rw [← zero_succ]
  rw [add_succ, add_zero]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

lemma Nat.add_one (n : Nat) : n + 1 = succ n := by
  rw [add_comm]
  exact one_add n

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  -- This proof was written by Issa.
  revert a; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  repeat rw [succ_add]
  rw [ih]

/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's `Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid.
This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the `abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right`. -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).IsPos := add_pos_left _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).IsPos := add_pos_right _ hb
  contradiction

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  -- This proof was written by Issa. New, cleaner version.
  rw [isPos_iff] at ha
  revert a; apply induction
  . tauto
  . intro n
    intro h1
    intro h2
    apply existsUnique_of_exists_of_unique
    use n
    intro y1 y2
    intro hy1 hy2
    apply succ_cancel at hy1
    apply succ_cancel at hy2
    rw [← hy2] at hy1
    exact hy1

lemma Nat.succ_eq (a:Nat) (ha: a.IsPos) : ∃ b, b++ = a := by
  apply Nat.uniq_succ_eq at ha
  apply ExistsUnique.exists ha


/-
  -- This proof was written by Issa. Old version that is messy.
  -- First, let's rewrite the definition of a positive natural number:
  rw [isPos_iff] at ha
  -- To prove unique existence, we break the proof into two parts: first we prove existence, then we prove uniqueness.
  apply existsUnique_of_exists_of_unique
  -- To prove existence, we use induction on a.
  revert a; apply induction
  -- For the base case, the statement is vacuously true since 0 is not positive.
  intro h
  contradiction
  -- Now for the inductive step. We don't actually need the inductive hypothesis, so we just use the _ to say we don't care what they are.
  intro a _
  intro _
  -- Since this is the inductive case, the number we are trying to show has a successor is already of the form a++, which means it automatically is a successor! So we just use the a we are given to complete the proof of existence:
  use a
  -- Now, for uniqueness. We start by unwrapping the quantifiers and hypotheses:
  intro y1 y2
  intro h1 h2
  -- At this point it's pretty obvious what to do. We substitute one of the a's in for the other, and use the injectivity of the successor to complete the proof.
  rw [← h2] at h1
  apply succ_cancel at h1
  exact h1
-/

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` operation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

-- This lemma was added by Issa.
lemma Nat.lt_iff_le_and_ne (n m : Nat) : n < m ↔ n ≤ m ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  -- This proof was written by Issa.
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . use 1
    rw [Nat.succ_eq_add_one]
  revert n; apply induction
  . intro h
    symm at h
    have : 0++ ≠ 0 := Nat.succ_ne 0
    contradiction
  intro n hn
  apply Nat.succ_ne_succ at hn
  exact hn

lemma Nat.lt_succ_self (n:Nat) : n < n++ := by
  rw [← gt_iff_lt]
  exact succ_gt_self n

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  -- This proof was written by Issa.
  rw [Nat.ge_iff_le, Nat.le_iff]
  use 0
  rw [Nat.add_zero]

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  -- This proof was written by Issa.
  rw [Nat.ge_iff_le]
  rw [Nat.ge_iff_le] at hab
  rw [Nat.ge_iff_le] at hbc
  rw [Nat.le_iff] at hab
  rw [Nat.le_iff] at hbc
  obtain ⟨ x, hx ⟩ := hab
  obtain ⟨ y, hy ⟩ := hbc
  rw [Nat.le_iff]
  use (y+x)
  rw [hx, hy]
  rw [Nat.add_assoc]

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  -- This proof was written by Issa.
  rw [Nat.ge_iff_le, Nat.le_iff] at hab
  rw [Nat.ge_iff_le, Nat.le_iff] at hba
  obtain ⟨ x, hx ⟩ := hab
  obtain ⟨ y, hy ⟩ := hba
  rw [hy] at hx
  rw [Nat.add_assoc] at hx
  nth_rewrite 1 [← Nat.add_zero a] at hx
  apply Nat.add_left_cancel at hx
  symm at hx
  apply Nat.add_eq_zero at hx
  have hyz : y = 0 := hx.left
  rw [hyz] at hy
  rw [Nat.add_zero] at hy
  symm at hy
  exact hy



/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  -- This proof was written by Issa.
  rw [Nat.ge_iff_le, Nat.ge_iff_le]
  constructor
  intro h
  rw [Nat.le_iff] at h
  obtain ⟨ x, hx ⟩ := h
  rw [Nat.le_iff]
  use x
  rw [hx]
  rw [Nat.add_assoc, Nat.add_assoc]
  rw [Nat.add_comm x c]
  intro h
  rw [Nat.le_iff] at h
  obtain ⟨ d, hd ⟩ := h
  use d
  rw [Nat.add_comm] at hd
  rw [Nat.add_comm b c] at hd
  rw [Nat.add_assoc] at hd
  apply add_left_cancel at hd
  exact hd

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  -- This proof was written by Issa.
  rw [Nat.lt_iff]
  constructor
  intro h
  let ⟨h1, h2⟩ := h
  rw [Nat.le_iff]
  obtain ⟨d, hd⟩ := h1
  rw [hd] at h2
  have hdpos: d ≠ 0 := by
    intro h'
    rw [h'] at h2
    rw [Nat.add_zero] at h2
    contradiction
  rw [← isPos_iff] at hdpos
  apply Nat.uniq_succ_eq at hdpos
  apply ExistsUnique.exists at hdpos
  rw [hd]
  obtain ⟨dp, hdp⟩ := hdpos
  rw [← hdp]
  use dp
  rw [Nat.add_succ]
  rw [Nat.succ_add]
  -- Now, for the other direction...
  intro h
  constructor
  rw [Nat.le_iff] at h
  obtain ⟨ d, hd ⟩ := h
  use (d++)
  rw [Nat.add_succ]
  rw [Nat.succ_add] at hd
  exact hd
  by_contra hc
  rw [Nat.le_iff] at h
  obtain ⟨ d, hd ⟩ := h
  rw [hc] at hd
  rw [Nat.succ_add] at hd
  rw [← Nat.add_succ] at hd
  nth_rewrite 1 [← Nat.add_zero b] at hd
  apply add_left_cancel at hd
  symm at hd
  apply Nat.succ_ne at hd
  exact hd


/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  -- This proof was written by Issa.
  rw [Nat.lt_iff_succ_le]
  constructor
  intro h
  obtain ⟨c, hc⟩ := h
  rw [Nat.succ_add] at hc
  rw [← Nat.add_succ] at hc
  use (c++)
  constructor
  rw [Nat.isPos_iff]
  apply Nat.succ_ne
  exact hc
  -- Now we do the other direction...
  intro h
  obtain ⟨ d, hd ⟩ := h
  let ⟨ h1, h2 ⟩ := hd
  rw [Nat.le_iff]
  apply Nat.uniq_succ_eq at h1
  apply ExistsUnique.exists at h1
  obtain ⟨ c, hc ⟩ := h1
  use c
  rw [← hc] at h2
  rw [Nat.add_succ] at h2
  rw [← Nat.succ_add] at h2
  exact h2

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  sorry

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by
      -- This sub-step was written by Issa.
      rw [Nat.le_iff]
      use b
      rw [Nat.zero_add]
  -- . have why : 0 ≤ b := b.zero_le -- this line was from the main repo, might be useful
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      -- This sub-step was written by Issa.
      rw [case2]
      rw [Nat.gt_iff_lt]
      rw [Nat.lt_iff_add_pos]
      use 1
      constructor
      rw [isPos_iff]
      rw [← Nat.zero_succ]
      exact Nat.succ_ne _
      rw [← Nat.zero_succ]
      rw [Nat.add_succ, Nat.add_zero]
    tauto
  have why : a++ > b := by
    -- This sub-step was written by Issa.
    rw [Nat.gt_iff_lt]
    rw [Nat.gt_iff_lt] at case3
    rw [Nat.lt_iff_add_pos]
    rw [Nat.lt_iff_add_pos] at case3
    obtain ⟨ d, hd ⟩ := case3
    let ⟨ hd1, hd2 ⟩ := hd
    use (d++)
    constructor
    rw [Nat.isPos_iff]
    apply Nat.succ_ne
    rw [hd2]
    rw [Nat.add_succ]
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    -- This part was done by Issa.
    use b
    rw [Nat.zero_add]
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        -- This part was done by Issa.
        by_contra h'
        rw [← h] at h'
        have ha : a++ > a := succ_gt_self a
        rw [Nat.le_iff_lt_or_eq] at h'
        rcases h' with h1 | h2
        apply Nat.not_lt_of_gt (a++) a
        constructor
        exact h1
        exact ha
        rw [← Nat.add_zero (a++)] at h2
        rw [Nat.succ_add] at h2
        rw [← Nat.add_succ] at h2
        nth_rewrite 2 [← Nat.add_zero a] at h2
        apply add_left_cancel at h2
        apply Nat.succ_ne at h2
        exact h2
      | isFalse h =>
        apply isTrue
        -- This part was done by Issa.
        rw [← Nat.lt_iff_succ_le]
        rw [Nat.lt_iff]
        rw [← Nat.le_iff]
        tauto
    | isFalse h =>
      apply isFalse
      -- This part was written by Issa.
      contrapose! h
      rw [← Nat.lt_iff_succ_le] at h
      rw [Nat.lt_iff] at h
      rw [← Nat.le_iff] at h
      tauto

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe


/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := by
    -- This proof was written by Issa.
    intro a b
    rw [Nat.lt_iff]
    rw [← Nat.le_iff]
    constructor
    intro h
    constructor
    exact h.left
    contrapose! h
    intro h'
    exact Nat.ge_antisymm h h'
    intro h
    constructor
    exact h.left
    have : b > a := by
      rw [Nat.le_iff_lt_or_eq] at h
      rw [Nat.le_iff_lt_or_eq] at h
      tauto
    rw [Nat.gt_iff_lt] at this
    rw [Nat.lt_iff] at this
    exact this.right
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    -- This part was written by Issa.
    intro a b
    rw [Nat.le_iff_lt_or_eq]
    rw [Nat.le_iff_lt_or_eq]
    have h := Nat.trichotomous
    specialize h a b
    tauto
  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

-- This lemma was added by Issa.
lemma Nat.le_succ_cancel {a b : Nat} (h : a++ ≤ b++) : a ≤ b := by
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at h
  rw [← Nat.ge_iff_le] at h
  rw [← Nat.add_ge_add_right] at h
  rw [Nat.ge_iff_le] at h
  exact h

-- This lemma was added by Issa.
lemma Nat.le_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [← Nat.ge_iff_le]
  rw [← Nat.ge_iff_le] at hab
  rw [← Nat.ge_iff_le] at hbc
  exact Nat.ge_trans hbc hab

-- This lemma was added by Issa.
lemma Nat.lt_trans {a b c : Nat} (hab : a < b) (hbc : b < c) : a < c := by
  rw [Nat.lt_iff] at hab
  rw [← Nat.le_iff] at hab
  rw [Nat.lt_iff] at hbc
  rw [← Nat.le_iff] at hbc
  have haleqc : a ≤ c := Nat.le_trans hab.left hbc.left
  have hanec : a ≠ c := by
    by_contra this
    rw [this] at hab
    have : b = c := by
      rw [← Nat.ge_iff_le] at hab
      rw [← Nat.ge_iff_le] at hbc
      apply Nat.ge_antisymm
      exact hab.left
      exact hbc.left
    tauto
  rw [Nat.lt_iff]
  rw [← Nat.le_iff]
  constructor
  exact haleqc
  exact hanec

-- This lemma was added by Issa.
lemma Nat.le_lt_trans {a b c : Nat} (hab : a ≤ b) (hbc : b < c) : a < c := by
  have h1 : b ≤ c := by
    rw [Nat.lt_iff] at hbc
    rw [← Nat.le_iff] at hbc
    exact hbc.left
  have h2 := Nat.le_trans hab h1
  rw [Nat.le_iff_lt_or_eq] at h2
  obtain hlt|heq := h2
  exact hlt
  rw [← heq] at hbc
  rw [Nat.lt_iff] at hbc
  rw [← Nat.le_iff] at hbc
  obtain ⟨ h2, h3 ⟩ := hbc
  have : b = a := by
    rw [← Nat.ge_iff_le] at hab
    rw [← Nat.ge_iff_le] at h2
    exact Nat.ge_antisymm hab h2
  contradiction

lemma Nat.le_lt_succ_split {a b c: Nat} (h : a ≤ b ∧ b < c++) : (a ≤ b ∧ b < c) ∨ b = c := by
  rw [Nat.lt_iff_succ_le] at h
  obtain ⟨ h0, h1 ⟩ := h
  apply le_succ_cancel at h1
  rw [le_iff_lt_or_eq] at h1
  rcases h1 with h2 | h3
  . left
    exact And.intro h0 h2
  right
  exact h3

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a+d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  let Q (n : Nat) := ∀ m', m₀ ≤ m' ∧ m' < n → P m'
  have hind_using_Q : ∀ m ≥ m₀, Q m → P m := hind
  have Qn : ∀ n, Q n := by
    apply induction
    . unfold Q
      intro m
      intro h
      rw [lt_iff] at h
      obtain ⟨ a, ha ⟩ := h.right.left
      symm at ha
      apply Nat.add_eq_zero at ha
      tauto
    intro n h
    have := trichotomous m₀ n
    rw [← or_assoc] at this
    rcases this with h1 | h2
    . rw [← le_iff_lt_or_eq] at h1
      rw [← ge_iff_le] at h1
      specialize hind_using_Q n
      have := hind_using_Q h1
      have := this h
      have : ∀ m, m₀ ≤ m ∧ m < n++ → P m := by
        intro m hm
        unfold Q at h
        specialize h m
        have := le_lt_succ_split hm
        rcases this with hi | heq
        . exact h hi
        rw [← heq] at this
        exact this
      exact this
    have : ¬∃m, m₀ ≤ m ∧ m < n++ := by
      intro hc
      obtain ⟨ m, hm ⟩ := hc
      have := le_lt_trans hm.1 hm.2
      rw [lt_iff_succ_le] at this
      apply le_succ_cancel at this
      rw [le_iff_lt_or_eq] at this
      rw [gt_iff_lt] at h2
      sorry
    unfold Q
    intro m hm
    have := this ⟨ m, hm ⟩
    contradiction
  intro m h
  specialize Qn (m++)
  unfold Q at Qn
  specialize Qn m
  have : m < m++ := lt_succ_self m
  rw [ge_iff_le] at h
  exact Qn (And.intro h this)



theorem Nat.strong_induction' {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  -- This proof was written by Issa.
  let Q (n : Nat) := ∀ m', m₀ ≤ m' ∧ m' < n → P m'
  have hind_using_Q : ∀ m, m ≥ m₀ → Q m → P m := hind
  have Qn : ∀ n, Q n := by
    apply induction
    . unfold Q
      intro m
      intro h
      rw [Nat.lt_iff] at h
      obtain ⟨ a, ha ⟩ := h.right.left
      symm at ha
      apply Nat.add_eq_zero at ha
      tauto
    . intro n
      intro h
      unfold Q
      intro m
      intro h1
      have : (m₀ ≤ m ∧ m < n) ∨ m = n := le_lt_succ_split h1
      obtain h2 | h3 := this
      . unfold Q at h
        specialize h m
        exact h h2
      . have h4 : m ≤ n++ := by
          rw [Nat.lt_iff_le_and_ne] at h1
          exact h1.right.left
        have h5 := Nat.le_trans h1.left h4
        have : m₀ ≠ n++ := by
          obtain ⟨ h6, h7 ⟩ := h1
          have h8 := Nat.le_lt_trans h6 h7
          rw [Nat.lt_iff] at h8
          exact h8.right
        have : m₀ ≤ n++ ∧ m₀ ≠ n++ := by tauto
        rw [← Nat.lt_iff_le_and_ne] at this
        rw [Nat.lt_iff_succ_le] at this
        apply Nat.le_succ_cancel at this
        rw [← Nat.ge_iff_le] at this
        specialize hind_using_Q n
        have h6 := hind_using_Q this
        have h7 := h6 h
        rw [h3]
        exact h7
  intro m h
  specialize Qn (m++)
  unfold Q at Qn
  specialize Qn m
  have : m < m++ := by
    rw [← Nat.gt_iff_lt]
    apply succ_gt_self
  rw [Nat.ge_iff_le] at h
  have h1 := And.intro h this
  apply Qn at h1
  exact h1

-- This lemma was added by Issa.
lemma Nat.eq_zero_of_le_zero (n : Nat) (h: n ≤ 0) : n = 0 := by
  rw [Nat.le_iff] at h
  obtain ⟨ a, ha ⟩ := h
  symm at ha
  apply Nat.add_eq_zero at ha
  exact ha.left

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  -- This proof was done by Issa.
  let Q (n : Nat) := P n → ∀ m, m ≤ n → P m
  have : ∀ n, Q n := by
    apply induction
    . unfold Q
      intro h
      intro m
      intro h1
      apply Nat.eq_zero_of_le_zero at h1
      rw [h1]
      exact h
    . intro n
      intro h
      unfold Q
      intro hPnpp
      specialize hind n
      have hpp := hPnpp
      apply hind at hPnpp
      unfold Q at h
      apply h at hPnpp
      intro m
      intro h1
      have : m ≤ n ∨ m = n++ := by
        have : m ≠ n++ → m ≤ n := by
          intro h2
          have h3 := And.intro h1 h2
          rw [← Nat.lt_iff_le_and_ne] at h3
          rw [Nat.lt_iff_succ_le] at h3
          apply Nat.le_succ_cancel at h3
          exact h3
        tauto
      rcases this with h2|h3
      apply hPnpp
      exact h2
      rw [h3]
      exact hpp
  specialize this n
  unfold Q at this
  exact this hn

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  intro h
  let Q (m : Nat) := P (n + m)
  have : ∀ m, Q m := by
    apply induction
    . unfold Q
      rw [Nat.add_zero]
      exact h
    . intro m
      intro hmind
      unfold Q at hmind
      specialize hind (n + m)
      apply hind at hmind
      rw [← Nat.add_succ] at hmind
      unfold Q
      exact hmind
  unfold Q at this
  intro m hm
  rw [Nat.ge_iff_le] at hm
  rw [Nat.le_iff] at hm
  obtain ⟨ a, ha ⟩ := hm
  specialize this a
  rw [← ha] at this
  exact this

lemma Nat.isPos_iff_gt_zero (n:Nat) : n.IsPos ↔ n > 0 := by
  constructor
  . intro h
    rw [Nat.isPos_iff] at h
    rw [Nat.gt_iff_lt]
    rw [Nat.lt_iff]
    constructor
    . use n
      rfl
    symm
    exact h
  . rw [Nat.isPos_iff]
    exact Nat.ne_of_gt n 0

lemma Nat.ge_zero (n:Nat) : n ≥ 0 := by
  use n
  rw [zero_add]

lemma Nat.succ_gt_zero (n:Nat) : n++ > 0 := by
  rw [gt_iff_lt]
  rw [Nat.lt_iff_succ_le]
  have := ge_zero n
  rw [ge_iff_le] at this
  rw [add_le_add_right 0 n 1] at this
  rw [add_one, add_one] at this
  exact this

end Chapter2
