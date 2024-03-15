/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.algebra.bilinear
import linear_algebra.kronecker_to_tensor
import linear_algebra.my_tensor_product
import linear_algebra.nacgor

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

private def mul_map_aux (𝕜 X : Type*) [is_R_or_C 𝕜]
  [normed_add_comm_group_of_ring X] [normed_space 𝕜 X] [smul_comm_class 𝕜 X X] [is_scalar_tower 𝕜 X X]
  [finite_dimensional 𝕜 X] :
  X →ₗ[𝕜] (X →L[𝕜] X) :=
{ to_fun := λ x,
  { to_fun := linear_map.mul 𝕜 X x,
    map_add' := map_add _,
    map_smul' := map_smul _ },
  map_add' := λ x y, by { ext, simp_rw [map_add, continuous_linear_map.coe_mk',
    linear_map.coe_mk, linear_map.add_apply, continuous_linear_map.add_apply],
    refl, },
  map_smul' := λ r x, by { 
    ext,
    simp_rw [smul_hom_class.map_smul, continuous_linear_map.coe_mk', linear_map.coe_mk,
      linear_map.smul_apply, continuous_linear_map.smul_apply],
    refl, } }

def linear_map.mul_to_clm (𝕜 X : Type*) [is_R_or_C 𝕜]
  [normed_add_comm_group_of_ring X] [normed_space 𝕜 X] [smul_comm_class 𝕜 X X] [is_scalar_tower 𝕜 X X]
  [finite_dimensional 𝕜 X] :
  X →L[𝕜] (X →L[𝕜] X) :=
{ to_fun := mul_map_aux 𝕜 X,
  map_add' := map_add _,
  map_smul' := smul_hom_class.map_smul _,
  cont := by { simp only [linear_map.mk_coe],
    exact map_continuous _, } }

lemma linear_map.mul_to_clm_apply {𝕜 X : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group_of_ring X] [normed_space 𝕜 X] [smul_comm_class 𝕜 X X] [is_scalar_tower 𝕜 X X]
  [finite_dimensional 𝕜 X] (x y : X) :
  linear_map.mul_to_clm 𝕜 X x y = x * y :=
rfl

