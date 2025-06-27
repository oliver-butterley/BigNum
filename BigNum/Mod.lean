import Mathlib
import BigNum.ModDefs
import BigNum.Convert

/-! # Correctness of mod related definitions.

-/


@[simp]
lemma isZero_of_empty : isZero [] := by
  exact trivial

@[simp]
lemma isOne_of_true : isOne [true] := by
  exact trivial

@[simp]
lemma listBoolToNat_of_isZero (bs : List Bool) : isZero bs ↔ listBoolToNat bs = 0 := by
  constructor
  · intro h
    induction bs with
    | nil => rfl
    | cons head tail ih => by_cases head <;> simp_all [isZero]
  · intro h
    induction bs with
    | nil =>
      simp_all
    | cons head tail ih => by_cases head <;> simp_all [isZero]

@[simp]
lemma listBoolToNat_of_isOne (bs : List Bool) : isOne bs ↔ listBoolToNat bs = 1 := by
  constructor
  · intro h
    cases bs with
    | nil => simp [isOne] at h
    | cons head tail =>
      cases head with
      | true =>
        cases tail with
        | nil => simp
        | cons t_head t_tail => simp_all [isOne, isZero]
      | false => simp [isOne] at h
  · intro h
    cases bs with
    | nil => simp [isOne] at h
    | cons head tail =>
      cases head with
      | true =>
        cases tail with
        | nil => simp
        | cons t_head t_tail => simp_all [isOne, isZero]
      | false => simp [isOne] at h

lemma isZero_tail {tail : List Bool} (h : ∃ k, listBoolToNat (true :: tail) = 2 ^ k) :
    isZero tail := by
  induction tail with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨k, hk⟩ := h
    obtain hk' | hk' : k = 0 ∨ 0 < k := by omega
    · simp_all
    · have ho : Odd (2 ^ k) := by simp [← hk]
      have he : Even (2 ^ k) := by exact (Nat.even_pow' <| Nat.ne_zero_of_lt hk').mpr (by norm_num)
      -- Surely there is a lemma `Odd m → Even m → False` instead of the next two lines?
      simp [Odd, Even] at ho he
      omega

lemma isPowTwo_of_isPowTwo_tail {tail} (h : isPowTwo tail) : isPowTwo (false :: tail) := by
  simpa [isPowTwo]

theorem isPowTwo_iff (bs : List Bool) :
  isPowTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k) := by
  constructor
  -- Forward direction
  · intro h
    induction bs with
    | nil => simp [isPowTwo] at h
    | cons head tail ih =>
      cases head with
      | true =>
        -- Case: bs = true :: tail
        refine ⟨by simp, Nat.size (listBoolToNat tail), ?_⟩
        simp_all [listBoolToNat, isPowTwo]
      | false =>
        -- Case: bs = false :: tail
        obtain ⟨k, hk⟩ := (ih h).2
        refine ⟨?_, k + 1, ?_⟩
        · simp_all [isPowTwo, listBoolToNat]
        · simp [hk]
          ring
  -- Reverse direction
  · intro ⟨h, hk⟩
    induction bs with
    | nil =>
      simp [listBoolToNat] at h
    | cons head tail ih =>
      cases head with
      | true =>
        -- Case: bs = true :: tail
        have := isZero_tail hk
        simp_all [isPowTwo]
      | false =>
        -- Case: bs = false :: tail
        have : 0 < listBoolToNat tail := by
          simp_all
        have := ih this
        obtain ⟨ℓ, hℓ⟩ : ∃ k, listBoolToNat tail = 2 ^ k := by
          obtain ⟨k, hk⟩ := hk
          obtain hc | hc : k = 0 ∨ 0 < k := by omega
          · simp_all
          · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := Nat.exists_eq_add_one.mpr hc
            use j
            simp_all  [hj, show 2 ^ (j + 1) = 2 * 2 ^ j by omega]
        apply isPowTwo_of_isPowTwo_tail
        simp_all

@[simp]
lemma removeTrailingZeros_of_empty : removeTrailingZeros [] = [] := by
  simp [removeTrailingZeros, removeLeadingZeros]

@[simp]
lemma removeLeadingZeros_of_false : removeLeadingZeros [false] = [] := by
  simp [removeLeadingZeros]

lemma removeLeadingZeros_of_head_true {bs : List Bool} :
    removeLeadingZeros (bs ++ [true]) = (removeLeadingZeros bs) ++ [true] := by
  induction bs using removeLeadingZeros.induct with
    | case1 => tauto
    | case2 t ih => simpa
    | case3 t => simp [removeTrailingZeros, removeLeadingZeros]

lemma removeLeadingZeros_of_head' {bs : List Bool} (h : removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = [] := by
  induction bs with
    | nil => simp
    | cons head tail ih =>
      have hc : head = false := by
        by_contra! hc
        simp [hc, removeLeadingZeros] at h
      replace h : removeLeadingZeros tail = [] := by
        simp_all [hc, removeLeadingZeros]
      simp [hc, removeLeadingZeros, ih h]

lemma removeLeadingZeros_of_head'' {bs : List Bool} (h : ¬ removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = (removeLeadingZeros bs) ++ [false] := by
  induction bs with
    | nil =>
      simp [removeLeadingZeros] at h
    | cons head tail ih =>
      by_cases hc : head
      · rw [hc] at h ⊢
        simp [removeLeadingZeros]
      · rw [eq_false_of_ne_true hc] at h ⊢
        have : ¬removeLeadingZeros tail = [] := by
          simp_all [removeLeadingZeros]
        simp [removeLeadingZeros, ih this]

lemma removeTrailingZeros_listBoolToNat (bs : List Bool) :
    listBoolToNat (removeTrailingZeros bs) = listBoolToNat bs := by
  induction bs with
    | nil => simp
    | cons h t ih =>
      simp [removeTrailingZeros, removeLeadingZeros]
      by_cases hh : h
      · simp [hh, removeLeadingZeros_of_head_true,  ← ih, removeTrailingZeros, removeLeadingZeros]
      · by_cases ht : removeLeadingZeros t.reverse = []
        · unfold removeTrailingZeros at ih
          rw [ht, List.reverse_nil, listBoolToNat_of_empty] at ih
          simp [eq_false_of_ne_true hh, removeLeadingZeros_of_head' ht, ← ih]
        · simpa [eq_false_of_ne_true hh, removeLeadingZeros_of_head'' ht]

@[simp]
lemma modPowTwoListBool_of_empty {as : List Bool} : modPowTwoListBool as [] = as := by
  by_cases hc : as = [] <;> simp [hc, modPowTwoListBool]

@[simp]
lemma modPowTwoListBool_of_true {as bs} : modPowTwoListBool as (true :: bs) = [] := by
  by_cases hc : as = [] <;> simp [hc, modPowTwoListBool]

@[simp]
lemma isPowTwo_of_isPowTwo {tail} (h : isPowTwo (false :: tail)) : isPowTwo (tail) := by
  simp_all [isPowTwo]

@[simp]
lemma isZero_of_isPowTwo {tail} (h : isPowTwo (true :: tail)) : isZero tail := by
  exact h

lemma simnple_yet_hard (A B : Nat) : 2 * (A % B) + 1 = (2 * A + 1) % (2 * B) := by
  have := Nat.mul_mod_mul_left 2 A B
  rw [← this]
  have : 1 = 1 % (2 * B) := by
    have : 2 * B ≠ 1 := by
      obtain hc | hc : B = 0 ∨ 1 ≤ B := by omega
      · simp [hc]
      · refine Ne.symm (Nat.ne_of_lt ?_)
        linarith
    exact Eq.symm ((fun {n} => Nat.one_mod_eq_one.mpr) this)
  nth_rw 1 [this]
  rw [Nat.add_mod]
  -- Surely this is true!
  sorry

lemma modPowTwoListBool_listBoolToNat (as bs : List Bool) (h : isPowTwo bs) :
    listBoolToNat (modPowTwoListBool as bs) = (listBoolToNat as) % (listBoolToNat bs) := by
  induction as, bs using modPowTwoListBool.induct with
    | case1 counter => simp [modPowTwoListBool]
    | case2 as has => simp
    | case3 ha ta tb ih =>
      specialize ih <| isPowTwo_of_isPowTwo h
      by_cases hc : ha
      · simp [hc, modPowTwoListBool, ih]
        have := simnple_yet_hard (listBoolToNat ta) (listBoolToNat tb)
        exact this
      · simpa [hc, modPowTwoListBool, ih] using
          (Nat.mul_mod_mul_left 2 (listBoolToNat ta) (listBoolToNat tb)).symm
    | case4 bs tail ht =>
      have := isZero_of_isPowTwo h
      have : listBoolToNat tail = 0 := by exact (listBoolToNat_of_isZero tail).mp h
      simp [modPowTwoListBool, this]
      exact Eq.symm (Nat.mod_one (listBoolToNat bs))
