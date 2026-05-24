import Mathlib.Tactic

variable (n : ℕ)

/- 1) n² + n is even. -/
lemma even_sq_add_self : Even (n ^ 2 + n) := by
induction n with
| zero => norm_num -- For n=0, this is just a calculation.
| succ n ih =>
  obtain ⟨m,hm⟩ := ih -- Choose m such that n ^ 2 + n = 2 * m
  use n + 1 + m -- We claim that then (n + 1) ^ 2 + (n + 1) = 2 * (m + n + 1).
  -- Rewrite to isolate (n ^ 2 + n) and use the induction hypothesis.
  nth_rewrite 7 [add_comm]
  rw [← add_assoc m, add_assoc, ← add_assoc m (m + n), ← add_assoc m, ← hm]
  ring -- The rest is using the ring axioms.

/- 2) n³ + 2n is divisible by 3. -/
example : 3 ∣ n ^ 3 + 2 * n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use n ^ 2 + n + 1 + m
  -- Rewrite to isolate (3 * m) and use the induction hypothesis.
  rw [mul_add 3, ← hm]
  ring

/- 3) 4n³ - n is divisible by 3. -/
-- We use the coercion to ℤ to avoid having to deal with subtraction on ℕ.
lemma three_div_four_times_cubed_sub_self : 3 ∣ (4 * n ^ 3 - n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 4 * n ^ 2 + 4 * n + 1 + m
  -- Rewrite to isolate (3 * m) and use the induction hypothesis.
  rw [mul_add 3, ← hm]
  push_cast
  ring

/- 4) n³ - n is divisible by 6. -/
-- We use the coercion to ℤ to avoid having to deal with subtraction on ℕ.
example : 6 ∣ (n ^ 3 - n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m, hm⟩ := ih
  have := even_sq_add_self n
  obtain ⟨l,hl⟩ := this
  have h' : 6 * (l : ℤ) = 3 * (n ^ 2 + n) := by
    norm_cast
    rw [hl]
    ring
  use l + m
  rw [mul_add, ← hm, h']
  push_cast
  ring

/- 5) 2n³ + 3n² + n is divisible by 6. -/
example : 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use n ^ 2 + 2 * n + 1 + m
  rw [mul_add 6, ← hm]
  ring

/- 6) n³ - 6n² + 14n is divisible by 3. -/
example : 3 ∣ (n ^ 3 - 6 * n ^ 2 + 14 * n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use n ^ 2 - 3 * n + 3 + m
  rw [mul_add, ← hm]
  push_cast
  ring

/- 7) 3ⁿ - 3 is divisible by 6 (for n ≥ 1).) -/
example : 6 ∣ (3 ^ (n + 1) - 3 : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 3 * m + 1
  have : 3 ^ (n + 1) = 6 * m + 3 := by
    rw [← hm]
    ring
  rw [pow_succ, this]
  ring

/- 8) n³ + (n + 1)³ + (n + 2)³ is divisible by 9. -/
example : 9 ∣ n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use n ^ 2 + 3 * n + 3 + m
  rw [mul_add, ← hm]
  ring

/- 9) 7²ⁿ - 2ⁿ is divisible by 47. -/
example : 47 ∣ (7 ^ (2 * n) - 2 ^ n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 7 ^ (2 * n) + m * 2
  rw [mul_add 47, ← mul_assoc, ← hm]
  ring

/- 10) 5ⁿ + 7 is divisible by 4. -/
example : 4 ∣ 5 ^ n + 7 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 5 ^ n + m
  rw [mul_add, ← hm]
  ring

/- 11) 5²ⁿ - 3²ⁿ is divisible by 8. -/
example : 8 ∣ (5 ^ (2 * n) - 3 ^ (2 * n) : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 2 * 5 ^ (2 * n) + m * 9
  rw [mul_add 8, ← mul_assoc 8 m, ← hm]
  ring

/- 12) 2³ⁿ + 13 is divisible by 7. -/
example : 7 ∣ 2 ^ (3 * n) + 13 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 2 ^ (3 * n) + m
  rw [mul_add 7, ← hm]
  ring

/- 13) aⁿ - 1 is divisible by a - 1. -/
example (a : ℕ) : (a - 1 : ℤ) ∣ a ^ n - 1 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use a ^ n + m
  rw [mul_add, ← hm]
  ring

/- 14) n⁷ - n is divisible by 7. -/
example : 7 ∣ (n ^ 7 - n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use n ^ 6 + 3 * n ^ 5 + 5 * n ^ 4 + 5 * n ^ 3 + 3 * n ^ 2 + n + m
  rw [mul_add, ← hm]
  push_cast
  ring

/- 15) 3ⁿ⁺¹ + 2³ⁿ⁺¹ is divisible by 5. -/
example : 5 ∣ 3 ^ (n + 1) + 2 ^ (3 * n + 1) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 2 ^ (3 * n + 1) + m * 3
  rw [mul_add 5, ← mul_assoc, ← hm]
  ring

/- 16) 3n⁵ + 5n³ + 7n is divisible by 15. -/
example : 15 ∣ 3 * n ^ 5 + 5 * n ^ 3 + 7 * n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 1 + n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n + m
  rw [mul_add 15, ← hm]
  ring

/- 17) 3²ⁿ + 7 is divisible by 8. -/
example : 8 ∣ 3 ^ (2 * n) + 7 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 3 ^ (2 * n) + m
  rw [mul_add 8, ← hm]
  ring

/- 18) n³ + 5n is divisible by 6. -/
example : 6 ∣ n ^ 3 + 5 * n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  have := even_sq_add_self n
  obtain ⟨l,hl⟩ := this
  have h' : 3 * (n ^ 2 + n) = 6 * l := by
    rw [hl]
    ring
  use 1 + l + m
  rw [mul_add 6, mul_add 6, ← h', ← hm]
  ring

/- 19) n⁴ - 4n² is divisible by 3. -/
example : 3 ∣ (n ^ 4 - 4 * n ^ 2 : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  have := three_div_four_times_cubed_sub_self n
  obtain ⟨l,hl⟩ := this
  use 2 * n ^ 2 - n - 1 + m + l
  rw [mul_add, mul_add, ← hm, ← hl]
  push_cast
  ring

/- 20) 10ⁿ + 3 * 4ⁿ⁺² + 5 is divisible by 9. -/
example : 9 ∣ 10 ^ n + 3 * 4 ^ (n + 2) + 5 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 4 ^ (n + 2) + 10 ^ n + m
  rw [mul_add, ← hm]
  ring

/- 21) 4ⁿ + 15n - 1 is divisible by 9. -/
lemma helper9 : (9 : ℤ) ∣ 3 * 4 ^ n + 15 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      obtain ⟨m,hm⟩ := ih
      use 4 ^ n + m
      rw [mul_add, ← hm]
      ring

example : 9 ∣ (4 ^ n + 15 * n - 1 : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  obtain ⟨l,hl⟩ := helper9 n
  use l + m
  rw [mul_add, ← hm, ← hl]
  push_cast
  ring

/- 22) 5²ⁿ + 24n -1 is divisible by 48. -/
lemma helper48 : (48 : ℤ) ∣ 24 * 5 ^ (2 * n) + 24 := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 12 * 5 ^ (2 * n) + m
  rw [mul_add 48, ← hm]
  ring

example : 48 ∣ (5 ^ (2 * n) + 24 * n - 1 : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  obtain ⟨l,hl⟩ := helper48 n
  use l + m
  rw [mul_add 48, ← hl, ← hm]
  push_cast
  ring

/- 23) 11ⁿ⁺¹ + 12²ⁿ⁻¹ is divisible by 133. -/
example : 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use 12 ^ (2 * n + 1) + m * 11
  rw [mul_add 133, ← mul_assoc, ← hm]
  ring

/- 24) (2a-1)ⁿ - 1 is even. -/
example (a : ℕ) : 2 ∣ ((2 * a + 1) ^ n - 1 : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use a * (2 * a + 1) ^ n + m
  rw [mul_add 2, ← hm]
  ring

/- 25) aⁿ⁺¹ + (a + 1)²ⁿ⁻¹ is divisible by a² + a + 1. -/
example (a : ℕ) : a ^ 2 + a + 1 ∣ a ^ (n + 2) + (a + 1) ^ (2 * n + 1) := by
induction n with
| zero => use 1
          ring
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use (a + 1) ^ (2 * n + 1) + m * a
  rw [mul_add _ _ (m * a), ← mul_assoc, ← hm]
  ring

/- 26) a²ⁿ⁺¹ - a is divisible by 6. -/
lemma helper6a : 6 ∣ ((n ^ 2 - 1) * n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  have := even_sq_add_self n
  obtain ⟨l,hl⟩ := this
  obtain ⟨m,hm⟩ := ih
  have : (6 * l : ℤ) = 3 * (n ^ 2 + n) := by
    rw_mod_cast [hl]
    ring
  use l + m
  rw [mul_add, ← hm, this]
  push_cast
  ring

lemma helper6b (a : ℕ) : 6 ∣ ((a ^ 2 - 1) * a ^ (2 * n + 1) : ℤ) := by
induction n with
| zero => rw [mul_zero, zero_add, pow_one]
          exact helper6a a
| succ n ih =>
  have := helper6a a
  obtain ⟨l,hl⟩ := this
  obtain ⟨m,hm⟩ := ih
  use l * ((a ^ 2 - 1) * a ^ (2 * n)) + m
  rw [mul_add 6, ← mul_assoc, ← hl, ← hm]
  ring

example (a : ℕ) : 6 ∣ (a ^ (2 * n + 1) - a : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  obtain ⟨l,hl⟩ := helper6b n a
  use l + m
  rw [mul_add 6, ← hm, ← hl]
  ring
