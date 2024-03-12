/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.big_operators.fin

/-!

# Useless and interesting fact(s) on naturals and integers

*Sonia* recently asked me:
  "Is there a way to prove that a number is divisible by 9, by looking at the sum of its digits?"
So here is the generalised version of the question.

## Main results

In both of the following results, `b` is a natural number greater than `1`.

* `nat_repr_mod_eq_sum_repr_mod`: this says that the remainder of dividing a number
  in base `b + 1` by `b` is equal to the remainder of dividing the sum of its digits by `b`
* `nat_dvd_repr_iff_nat_dvd_sum_repr`: this says that a number in base `b + 1` is divisible by `b`
  if and only if the sum of its digits is divisible by `b`

-/

open_locale big_operators

/-- `(∑ i, x i) % a = (∑ i, (x i % a)) % a` -/
lemma int.sum_mod {n : ℕ} (x : fin n → ℤ) (a : ℤ) :
  (∑ i, x i) % a = (∑ i, (x i % a)) % a :=
begin
  induction n with d hd generalizing x a,
  { refl, },
  { let x' : fin d → ℤ := λ i, x i.succ,
    have hx' : ∀ i, x' i = x i.succ := λ i, rfl,
    simp_rw [fin.sum_univ_succ],
    rw [int.add_mod],
    simp_rw [← hx', int.mod_add_cancel_left],
    rw [hd],
    simp_rw [← hx', int.mod_mod], },
end

/- `n.succ % n = 1` if `1 < n` -/
lemma fin.succ_mod_self {n : ℕ} (hn : 1 < n) :
  n.succ % n = 1 :=
by
{ rw [nat.succ_eq_add_one, nat.add_mod, nat.mod_self, zero_add, nat.mod_mod],
  exact nat.mod_eq_of_lt hn, }

/-- `a.succ ^ n % a = 1` when `1 < a`  -/
lemma fin.succ_pow_mod_self {n a : ℕ} (ha : 1 < a) :
  a.succ ^ n % a = 1 :=
begin
  induction n with d hd generalizing a ha,
  { rw [pow_zero],
    exact nat.mod_eq_of_lt ha, },
  { rw [nat.pow_mod] at ⊢,
    simp_rw [nat.pow_mod (nat.succ _)] at hd,
    specialize hd ha,
    rw [fin.succ_mod_self ha, one_pow] at hd ⊢,
    exact hd, },
end

/- `(a * b.succ ^ n) % b = a % b` -/
lemma int.mul_nat_succ_pow_mod_nat (a : ℤ) {b n : ℕ} (hb : 1 < b) :
  (a * ((b : ℕ).succ ^ n : ℕ)) % (b : ℕ) = a % b :=
begin
  rw [int.mul_mod, int.of_nat_mod, fin.succ_pow_mod_self hb, int.of_nat_one, mul_one, int.mod_mod],
end

/--
 `(∑ i, (x i * a.succ ^ i)) % a = (∑ i, x i) % a`
-/
lemma nat_repr_mod_eq_sum_repr_mod {a n : ℕ} (x : fin n → ℤ)
  (ha : 1 < a) :
  (∑ i, x i * (a.succ : ℕ) ^ (i : ℕ)) % a = (∑ i, x i) % a :=
begin
  induction n with d hd generalizing x,
  { intros,
    refl, },
  { simp_rw [fin.sum_univ_succ, fin.coe_zero, pow_zero, mul_one, fin.coe_succ, int.mod_add_cancel_left],
    let x' : fin d → ℤ := λ i, x i.succ,
    have hx' : ∀ i, x' i = x i.succ := λ i, rfl,
    simp_rw [← nat.succ_eq_add_one, ← hx', hd x', hx'],
    rw [int.sum_mod],
    simp_rw [← hx'],
    rw [← int.mod_mod, int.mod_mod],
    have : ∀ (c : ℤ) (d : ℕ), c * (a.succ : ℕ) ^ d % a = c % a :=
    λ c d, calc c * (a.succ : ℕ) ^ d % a = c * ((a.succ : ℕ) ^ d : ℕ) % (a : ℕ) :
    by simp_rw [int.coe_nat_pow]
      ... = c % a : int.mul_nat_succ_pow_mod_nat _ ha,
    simp_rw [this, ← int.sum_mod], },
end

/--
  `a ∣ (∑ i, (x i * a.succ ^ i)) ↔ a ∣ (∑ i, x i)`
  in other words, a number in base `a.succ` is divisible by `a`, if and only if
  the sum of its digits is divisible by `a`
-/
lemma nat_dvd_repr_iff_nat_dvd_sum_repr {a n : ℕ} (x : fin n → ℤ) (ha : 1 < a) :
  (a : ℤ) ∣ (∑ i, x i * (a.succ : ℕ) ^ (i : ℕ))
    ↔ (a : ℤ) ∣ (∑ i, x i) :=
begin
  simp_rw [int.dvd_iff_mod_eq_zero, nat_repr_mod_eq_sum_repr_mod _ ha],
end

/--
 most natural example:
 `9 ∣ ∑ i, (x i * 10 ^ i) ↔ 9 ∣ ∑ i, x i`
 in other words, a number (in base `10`) is divisible by `9`, if and only if
 the sum of its digits is divisible by `9`
-/
example {n : ℕ} (x : fin n → ℤ) :
  9 ∣ (∑ i, x i * 10 ^ (i : ℕ)) ↔ 9 ∣ (∑ i, x i) :=
nat_dvd_repr_iff_nat_dvd_sum_repr x (by norm_num)

/-- so when the base is `8`, then a number in base `8` is divisible by `7`,
 if and only if the sum of its digits is divisible by `7` -/
example {n : ℕ} (x : fin n → ℤ) :
  7 ∣ (∑ i, x i * 8 ^ (i : ℕ)) ↔ 7 ∣ (∑ i, x i) :=
nat_dvd_repr_iff_nat_dvd_sum_repr _ (by norm_num)
