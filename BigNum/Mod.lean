import Mathlib
import BigNum.ModDefs
import BigNum.Convert

/-! # Correctness of mod related definitions.

-/

-- @[simp]
-- lemma listBoolToNat_of_isZero (bs : List Bool) (h : isZero bs) : listBoolToNat bs = 0 := by
--   induction bs with
--   | nil => rfl
--   | cons head tail ih => by_cases head <;> simp_all [isZero]

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

theorem isPowerOfTwo_correct (bs : List Bool) :
  isPowerOfTwo bs ↔ (listBoolToNat bs > 0 ∧ ∃ k, listBoolToNat bs = 2^k) := by
  constructor
  -- Forward direction
  · intro h
    induction bs with
    | nil => simp [isPowerOfTwo] at h
    | cons head tail ih =>
      cases head with
      | true =>
        refine ⟨by simp, Nat.size (listBoolToNat tail), ?_⟩
        simp_all [listBoolToNat, isPowerOfTwo]
      | false =>
        obtain ⟨k, hk⟩ := (ih h).2
        refine ⟨?_, k + 1, ?_⟩
        · simp_all [isPowerOfTwo, listBoolToNat]
        · simp [hk]
          ring
  -- Reverse direction
  · intro h
    sorry
    -- induction bs with
    -- | nil =>
    --   simp [listBoolToNat] at h
    --   cases' h with h1 h2
    --   contradiction
    -- | cons head tail ih =>
    --   cases head with
    --   | true =>
    --     -- Case: bs = true :: tail
    --     simp [listBoolToNat] at h
    --     cases' h with h1 h2
    --     cases' h2 with k hk
    --     simp [isPowerOfTwo]
    --     -- Need to show isZero tail
    --     -- We have 2 * listBoolToNat tail + 1 = 2^k
    --     -- This means listBoolToNat tail = (2^k - 1) / 2
    --     -- Since 2^k is even for k > 0, we need k = 0
    --     -- So listBoolToNat tail = 0, which means isZero tail
    --     have h_even : k = 0 := by
    --       by_contra h_ne
    --       have k_pos : k > 0 := Nat.pos_of_ne_zero h_ne
    --       have : 2^k ≥ 2 := Nat.pow_le_pow_of_le_right (by norm_num) k_pos
    --       have : 2 * listBoolToNat tail + 1 ≥ 2 := by rw [← hk]; exact this
    --       have : 2 * listBoolToNat tail ≥ 1 := Nat.le_sub_of_add_le this
    --       have : listBoolToNat tail > 0 := by
    --         cases' listBoolToNat tail with n
    --         · simp at this
    --         · simp
    --       -- But then 2^k = 2 * listBoolToNat tail + 1 is odd
    --       -- while 2^k for k > 0 is even, contradiction
    --       rw [hk] at this
    --       have : Odd (2^k) := by
    --         rw [← hk]
    --         simp [Odd, Nat.add_mod]
    --       have : Even (2^k) := Nat.even_pow_of_pos k_pos
    --       exact Nat.odd_iff_not_even.mp this this
    --     rw [h_even] at hk
    --     simp at hk
    --     have : listBoolToNat tail = 0 := by linarith
    --     exact isZero_implies_listBoolToNat_zero tail |>.mpr this
    --   | false =>
    --     -- Case: bs = false :: tail
    --     simp [listBoolToNat] at h
    --     cases' h with h1 h2
    --     cases' h2 with k hk
    --     simp [isPowerOfTwo]
    --     apply ih
    --     constructor
    --     · -- Show listBoolToNat tail > 0
    --       have : 2 * listBoolToNat tail = 2^k := hk
    --       have : listBoolToNat tail = 2^k / 2 := by
    --         rw [← this]
    --         simp [Nat.mul_div_cancel]
    --       cases k with
    --       | zero =>
    --         simp at this
    --         rw [this] at hk
    --         simp at hk
    --         contradiction
    --       | succ k' =>
    --         rw [this]
    --         simp [Nat.pow_succ, Nat.div_mul_cancel]
    --         exact Nat.pow_pos (by norm_num) k'
    --     · -- Show ∃ j, listBoolToNat tail = 2^j
    --       cases k with
    --       | zero =>
    --         simp at hk
    --         contradiction
    --       | succ k' =>
    --         use k'
    --         have : 2 * listBoolToNat tail = 2^(k' + 1) := hk
    --         have : 2 * listBoolToNat tail = 2 * 2^k' := by simp [Nat.pow_succ] at this; exact this
    --         exact Nat.mul_left_cancel this
