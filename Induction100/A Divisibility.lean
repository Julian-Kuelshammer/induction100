import Mathlib.Tactic

variable (n : ℕ)

/- 1) n ^ 2 + n is even. -/
lemma even_sq_add_self : Even (n ^ 2 + n) := by
induction n with
| zero => norm_num -- For n=0, this is just a calculation.
| succ n ih =>
  obtain ⟨m,hm⟩ := ih -- Choose m such that n ^ 2 + n = 2 * m
  use m + n + 1 -- We claim that then (n + 1) ^ 2 + (n + 1) = 2 * (m + n + 1).
  -- Rewrite to isolate (n ^ 2 + n) and use the induction hypothesis.
  rw [add_assoc m]
  nth_rewrite 5 [add_comm]
  rw [add_assoc, ← add_assoc m, ← hm]
  ring -- The rest is using the ring axioms.

/- 2) n ^ 3 + 2 * n is divisible by 3. -/
example : 3 ∣ n ^ 3 + 2 * n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use m + n ^ 2 + n + 1
  -- Rewrite to isolate (3 * m) and use the induction hypothesis.
  rw [mul_add 3, mul_add 3, mul_add 3, ← hm]
  ring

/- 3) 4 * n ^ 3 - n is divisible by 3. -/
-- We use the coercion to ℤ to avoid having to deal with subtraction on ℕ.
example : 3 ∣ (4 * n ^ 3 - n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use m + 4 * n ^ 2 + 4 * n + 1
  -- Rewrite to isolate (3 * m) and use the induction hypothesis.
  rw [add_assoc m, mul_add 3, mul_add 3, ← hm]
  push_cast
  ring

/- 4) n ^ 3 - n is divisible by 6. -/
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
  use m + l
  rw [mul_add, ← hm, h']
  push_cast
  ring

/- 5) 2 * n ^ 3 + 3 * n ^ 2 + n is divisible by 6. -/
example : 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + n := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use m + n ^ 2 + 2 * n + 1
  rw [add_assoc m, mul_add 6, mul_add 6, ← hm]
  ring

/- 6) n ^ 3 - 6 * n ^ 2 + 14 * n is divisible by 3. -/
example : 3 ∣ (n ^ 3 - 6 * n ^ 2 + 14 * n : ℤ) := by
induction n with
| zero => norm_num
| succ n ih =>
  obtain ⟨m,hm⟩ := ih
  use m + n ^ 2 - 3 * n + 3
  rw [mul_add, mul_sub, mul_add, ← hm]
  push_cast
  ring

/- 7) 3 ^ n - 3 is divisible by 6 (for n ≥ 1).) -/
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
