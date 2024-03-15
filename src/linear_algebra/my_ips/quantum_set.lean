/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.rank_one
import linear_algebra.my_ips.functional
import linear_algebra.nacgor

/-!

# Quantum Set

This file defines the structure of a quantum set.

A quantum set is defined as a star-algebra `A` over `ℂ` with a positive element `Q` such that
  `Q` is invertible and a sum of rank-one operators (in other words, positive definite).
The quantum set is also equipped with a faithful positive linear functional `φ` on `A`,
  which is used to define the inner product on `A`, i.e., `⟪x, y⟫_ℂ = φ (star x * y)`.
The quantum set is also equipped with a `trace` functional on `A` such that `φ x = trace (Q * x)`.

## Main definitions

* `quantum_set A` is a structure that defines a quantum set.
* `quantum_set.mod_aut A t` defines the modular automorphism of a quantum set, which is
  a family of automorphisms of `A` parameterized by `t : ℝ`, given by `x ↦ Q^(-t) * x * Q^t`,
  where `Q` is the unique positive definite element in `A` given by the quantum set structure.

-/

-- def star_ordered_ring.pos_add_submonoid (A : Type*) [semiring A]
--   [partial_order A] [star_ordered_ring A] : submonoid A :=
-- { carrier := { x | 0 < x },
--   add_mem' := λ x y hx hy,
--   by { simp only [set.mem_set_of_eq, add_nonneg hx hy], }
--    }

-- local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class
class quantum_set (A : Type*) :=
(to_normed_add_comm_group_of_ring : normed_add_comm_group_of_ring A)
(to_inner_product_space : inner_product_space ℂ A)
(to_partial_order : partial_order A)
(to_star_ordered_ring : star_ordered_ring A)
(to_has_smul_comm_class : smul_comm_class ℂ A A)
(to_is_scalar_tower : is_scalar_tower ℂ A A)
(to_finite_dimensional : finite_dimensional ℂ A)
(to_has_inv : has_inv A)
(φ : module.dual ℂ A)
(hφ : φ.is_faithful_pos_map)
(inner_eq : ∀ x y : A, ⟪x, y⟫_ℂ = φ (star x * y))
(functional_adjoint_eq :
  let _inst : algebra ℂ A := algebra.of_is_scalar_tower_smul_comm_class in
  (linear_map.adjoint φ) = algebra.linear_map ℂ A)
(A_pos := { x : A // 0 < x })
-- (A_pos_has_one : has_one A_pos)
(A_pos_has_pow : has_pow A_pos ℝ)
(A_pos_has_inv : has_inv A_pos)
(A_pos_pow_mul : ∀ (x : A_pos) (t s : ℝ),
  ((x ^ t : A_pos) : A) * ((x ^ s : A_pos) : A) = ↑(x ^ (t + s)))
(A_pos_pow_zero : ∀ (x : A_pos), ↑(x ^ (0 : ℝ)) = (1 : A))
(A_pos_pow_one : ∀ (x : A_pos), x ^ (1 : ℝ) = x)
(A_pos_pow_neg : ∀ (x : A_pos) (t : ℝ), (x ^ (-t : ℝ)) = (x ^ t)⁻¹)
(A_pos_inv_coe : ∀ (x : A_pos), (x : A)⁻¹ = (x⁻¹ : A_pos))
(Q : A_pos)
-- (Q_is_pos : ∃ x : A, (Q : A) = star x * x)
-- (has_lt : has_lt A)
-- (Q_is_pos_def : 0 < Q)
(trace : module.dual ℂ A)
(trace_is_tracial : trace.is_tracial)
(functional_eq : ∀ x : A, φ x = trace (Q * x))

attribute [instance] quantum_set.to_normed_add_comm_group_of_ring
attribute [instance] quantum_set.to_inner_product_space
attribute [instance] quantum_set.to_partial_order
attribute [instance] quantum_set.to_star_ordered_ring
attribute [instance] quantum_set.to_has_smul_comm_class
attribute [instance] quantum_set.to_is_scalar_tower
attribute [instance] quantum_set.to_finite_dimensional
attribute [instance] quantum_set.to_has_inv
attribute [instance] quantum_set.A_pos_has_pow
attribute [instance] quantum_set.A_pos_has_inv

namespace quantum_set

local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class
@[simps] def mod_aut (A : Type*) [quantum_set A] (t : ℝ) :
  A ≃ₐ[ℂ] A :=
  let A_pos := {x : A // 0 < x} in
  let Q : A_pos := quantum_set.Q in
{ to_fun := λ x, ↑(Q ^ (-t) : A_pos) * x * ↑(Q ^ t : A_pos),
  inv_fun := λ x, ↑(Q ^ t : A_pos) * x * ↑(Q ^ (-t) : A_pos),
  left_inv := λ x,
  by
  { calc ↑(Q ^ t) * (↑(Q ^ -t) * x * ↑(Q ^ t)) * ↑(Q ^ -t)
    = (↑(Q ^ t) * ↑(Q ^ t)⁻¹) * x * (↑(Q ^ t) * ↑(Q ^ t)⁻¹) :
  by { simp_rw [mul_assoc, A_pos_pow_neg], }
  ... = ↑(Q ^ (t + -t)) * x * ↑(Q ^ (t + -t)) : by
  { rw [← A_pos_pow_neg, A_pos_pow_mul], }
  ... = x : by { simp_rw [add_neg_self, A_pos_pow_zero, one_mul, mul_one], }, },
  right_inv := λ x,
  by
  { calc ↑(Q ^ -t) * (↑(Q ^ t) * x * ↑(Q ^ -t)) * ↑(Q ^ t)
    = (↑(Q ^ t)⁻¹ * ↑(Q ^ t)) * x * (↑(Q ^ t)⁻¹ * ↑(Q ^ t)) :
    by { simp only [mul_assoc, A_pos_pow_neg], }
    ... = ↑(Q ^ (-t + t)) * x * ↑(Q ^ (-t + t)) :
    by simp_rw [← A_pos_pow_neg, A_pos_pow_mul]
    ... = x : by { simp_rw [neg_add_self, A_pos_pow_zero, one_mul, mul_one], }, },
  map_mul' := λ x y,
  by { 
    calc ↑(Q ^ -t : A_pos) * (x * y) * ↑(Q ^ t : A_pos)
      = ↑(Q ^ -t) * x * (↑(Q ^ t) * ↑(Q ^ -t)) * y * ↑(Q ^ t) :
    by simp_rw [A_pos_pow_mul, add_neg_self, A_pos_pow_zero, mul_one, mul_assoc]
    ... = (↑(Q ^ -t) * x * ↑(Q ^ t)) * (↑(Q ^ -t) * y * ↑(Q ^ t)) :
    by simp_rw [mul_assoc], },
  map_add' := λ x y, by { simp_rw [mul_add, add_mul], },
  commutes' := λ r, by { simp_rw [algebra.algebra_map_eq_smul_one, mul_smul_comm, mul_one,
    smul_mul_assoc, A_pos_pow_mul, neg_add_self, A_pos_pow_zero], } }

variables {A : Type*} [quantum_set A]
lemma mod_aut_trans (t s : ℝ) :
  (mod_aut A t).trans (mod_aut A s) = mod_aut A (t + s) :=
begin
  ext x,
  simp_rw [alg_equiv.trans_apply, mod_aut_apply, mul_assoc, A_pos_pow_mul,
    ← mul_assoc, A_pos_pow_mul, neg_add, add_comm],
end

lemma mod_aut_neg (t : ℝ) :
  mod_aut A (-t) = (mod_aut A t).symm :=
begin
  ext1,
  simp_rw [mod_aut_apply, mod_aut_symm_apply, neg_neg],
end

end quantum_set
