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
      -- Surely there is a lemma in mathlib instead of the next two lines?
      simp [Odd, Even] at ho he
      omega

lemma isPowTwo_of_isPowTwo_tail {tail} (h : isPowerOfTwo tail) : isPowerOfTwo (false :: tail) := by
  simpa [isPowerOfTwo]

theorem isPowerOfTwo_iff (bs : List Bool) :
  isPowerOfTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k) := by
  constructor
  -- Forward direction
  · intro h
    induction bs with
    | nil => simp [isPowerOfTwo] at h
    | cons head tail ih =>
      cases head with
      | true =>
        -- Case: bs = true :: tail
        refine ⟨by simp, Nat.size (listBoolToNat tail), ?_⟩
        simp_all [listBoolToNat, isPowerOfTwo]
      | false =>
        -- Case: bs = false :: tail
        obtain ⟨k, hk⟩ := (ih h).2
        refine ⟨?_, k + 1, ?_⟩
        · simp_all [isPowerOfTwo, listBoolToNat]
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
        simp_all [isPowerOfTwo]
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

lemma removeLeadingZeros_of_head {bs : List Bool} :
    removeLeadingZeros (bs ++ [true]) = (removeLeadingZeros bs) ++ [true] := by
  induction bs using removeLeadingZeros.induct with
    | case1 => tauto
    | case2 t ih => simpa
    | case3 t => simp [removeTrailingZeros, removeLeadingZeros]

lemma removeLeadingZeros_of_head' {bs : List Bool} (h : removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = [] := by
  sorry

lemma removeLeadingZeros_of_head'' {bs : List Bool} (h : ¬ removeLeadingZeros bs = []) :
    removeLeadingZeros (bs ++ [false]) = (removeLeadingZeros bs) ++ [false] := by
  sorry

lemma removeTrailingZeros_listBoolToNat (bs : List Bool) :
    listBoolToNat (removeTrailingZeros bs) = listBoolToNat bs := by
  induction bs with
    | nil => simp
    | cons h t ih =>
      simp [removeTrailingZeros, removeLeadingZeros]
      by_cases hh : h
      · simp [hh, removeLeadingZeros_of_head,  ← ih, removeTrailingZeros, removeLeadingZeros]
      · by_cases ht : removeLeadingZeros t.reverse = []
        ·
          have : h = false := by exact eq_false_of_ne_true hh
          have := removeLeadingZeros_of_head' ht
          rw [eq_false_of_ne_true hh, this]
          simp
          rw [← ih]

          simp [hh, removeLeadingZeros_of_head' ht,  ← ih, removeTrailingZeros, removeLeadingZeros]

          sorry
        ·
          sorry
