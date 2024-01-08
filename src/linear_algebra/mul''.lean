/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.algebra.bilinear
import linear_algebra.kronecker_to_tensor
import linear_algebra.my_tensor_product

/-!

# linear_map.mul''

this defines the multiplication map $M_{n\times n} \to M_n$

-/

open matrix
open_locale matrix kronecker big_operators

variables {R A B : Type*} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

lemma commutes_with_unit_iff (f : A →ₗ[R] B) :
  f ∘ₗ (algebra.linear_map R A) = algebra.linear_map R B
    ↔ f 1 = 1 :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, algebra.linear_map_apply,
    algebra.algebra_map_eq_smul_one, smul_hom_class.map_smul],
  refine ⟨λ h, _, λ h x, by rw h⟩,
  { specialize h 1,
    simp_rw [one_smul] at h,
    exact h, },
end

lemma commutes_with_mul'_iff (f : A →ₗ[R] B) :
  (linear_map.mul' R B) ∘ₗ (tensor_product.map f f) = f ∘ₗ (linear_map.mul' R A)
    ↔ ∀ x y : A, f (x * y) = f x * f y :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.comp_apply, tensor_product.map_apply,
    linear_map.mul'_apply, eq_comm],
end

-- MOVE:
lemma matrix.kronecker_product.ext_iff {R P n₁ n₂ : Type*}
  [fintype n₁] [fintype n₂] [comm_semiring R]
  [add_comm_monoid P] [module R P] [decidable_eq n₁] [decidable_eq n₂]
  {g h : matrix (n₁ × n₂) (n₁ × n₂) R →ₗ[R] P} :
  g = h ↔ ∀ (x : matrix n₁ n₁ R) (y : matrix n₂ n₂ R), g (x ⊗ₖ y) = h (x ⊗ₖ y) :=
begin
  refine ⟨λ h x y, by rw h, λ h, _⟩,
  rw [linear_map.ext_iff],
  intros x,
  rw kmul_representation x,
  simp_rw [map_sum, smul_hom_class.map_smul, h _ _],
end
