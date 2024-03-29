/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.tensor_hilbert
import linear_algebra.my_ips.nontracial
import linear_algebra.direct_sum_from_to
import linear_algebra.pi_direct_sum

/-!
 # Frobenius equations

 This file contains the proof of the Frobenius equations.
-/

variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]
  {φ : module.dual ℂ (matrix n n ℂ)} (hφ : φ.is_faithful_pos_map)
  {ψ : module.dual ℂ (matrix p p ℂ)} (hψ : ψ.is_faithful_pos_map)
  {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {θ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hθ : Π i, fact (θ i).is_faithful_pos_map]

open_locale matrix kronecker tensor_product big_operators functional
open matrix

-- def linear_map.is_faithful_pos_map.tensor_pow (x : ℕ) :
--   ⨂[ℂ]^x (matrix n n ℂ) →ₗ[ℂ] ℂ :=
-- { to_fun := λ a, by { simp only [tensor_algebra] } }
noncomputable def module.dual.tensor_mul
  {n p : Type*}
  (φ₁ : module.dual ℂ (matrix n n ℂ))
  (φ₂ : module.dual ℂ (matrix p p ℂ)) :
  module.dual ℂ (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) :=
((tensor_product.lid ℂ ℂ) : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ∘ₗ (tensor_product.map φ₁ φ₂)

lemma module.dual.tensor_mul_apply (φ₁ : module.dual ℂ (matrix n n ℂ))
  (φ₂ : module.dual ℂ (matrix p p ℂ)) (x : matrix n n ℂ) (y : matrix p p ℂ) :
  (φ₁.tensor_mul φ₂) (x ⊗ₜ[ℂ] y) = φ₁ x * φ₂ y :=
rfl
lemma module.dual.tensor_mul_apply' (φ₁ : module.dual ℂ (matrix n n ℂ)) (φ₂ : module.dual ℂ (matrix p p ℂ))
  (x : matrix n n ℂ ⊗[ℂ] matrix p p ℂ) :
  φ₁.tensor_mul φ₂ x = ∑ i j k l, (x.to_kronecker (i,k) (j,l))
    * (φ₁ (std_basis_matrix i j (1 : ℂ)) * φ₂ (std_basis_matrix k l (1 : ℂ))) :=
begin
  simp_rw [← module.dual.tensor_mul_apply, ← smul_eq_mul, ← smul_hom_class.map_smul, ← map_sum],
  rw ← x.matrix_eq_sum_std_basis,
end

lemma module.dual.tensor_mul_apply'' (φ₁ : module.dual ℂ (matrix n n ℂ)) (φ₂ : module.dual ℂ (matrix p p ℂ))
  (a : matrix (n × p) (n × p) ℂ) :
  ((φ₁.tensor_mul φ₂).comp kronecker_to_tensor_product) a
    = (φ₁.matrix ⊗ₖ φ₂.matrix ⬝ a).trace :=
begin
  have : (φ₁.matrix ⊗ₖ φ₂.matrix ⬝ a).trace = ((trace_linear_map _ ℂ ℂ).comp
    (linear_map.mul_left ℂ (φ₁.matrix ⊗ₖ φ₂.matrix))) a :=
  rfl,
  simp_rw [this],
  clear this,
  revert a,
  rw [← linear_map.ext_iff, kronecker_product.ext_iff],
  intros x y,
  simp_rw [linear_map.comp_apply, kronecker_to_tensor_product_apply,
    module.dual.tensor_mul_apply, linear_map.mul_left_apply, trace_linear_map_apply,
    mul_eq_mul, ← mul_kronecker_mul, trace_kronecker, module.dual.apply],
end

lemma module.dual.tensor_mul_matrix (φ₁ : module.dual ℂ (matrix n n ℂ)) (φ₂ : module.dual ℂ (matrix p p ℂ)) :
  module.dual.matrix ((φ₁.tensor_mul φ₂).comp kronecker_to_tensor_product) = φ₁.matrix ⊗ₖ φ₂.matrix :=
begin
  symmetry,
  apply module.dual.apply_eq_of,
  simp_rw [← module.dual.tensor_mul_apply'' φ₁ φ₂],
  intros,
  refl,
end

@[instance] def module.dual.is_faithful_pos_map.tensor_mul
  {φ₁ : module.dual ℂ (matrix n n ℂ)}
  {φ₂ : module.dual ℂ (matrix p p ℂ)} [hφ₁ : fact φ₁.is_faithful_pos_map]
  [hφ₂ : fact φ₂.is_faithful_pos_map] :
  fact (module.dual.is_faithful_pos_map ((φ₁.tensor_mul φ₂).comp kronecker_to_tensor_product)) :=
begin
  apply fact.mk,
  rw [module.dual.is_faithful_pos_map_iff_of_matrix, module.dual.tensor_mul_matrix],
  exact pos_def.kronecker hφ₁.elim.matrix_is_pos_def hφ₂.elim.matrix_is_pos_def,
end

lemma matrix.kronecker_to_tensor_product_adjoint
  [hφ : fact φ.is_faithful_pos_map] [hψ : fact ψ.is_faithful_pos_map] :
  (@tensor_product.to_kronecker ℂ n p _ _ _ _ _ :
    (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) →ₗ[ℂ] matrix (n × p) (n × p) ℂ)
  -- = @linear_map.adjoint ℂ (matrix (n × p) (n × p) ℂ) (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) _
  --   (nacg_th hφ hψ) (nacg_tt hφ hψ) (ips_th hφ hψ) (ips_tt hφ hψ) _ _
  = (kronecker_to_tensor_product
    : (matrix (n × p) (n × p) ℂ) →ₗ[ℂ] (matrix n n ℂ ⊗[ℂ] matrix p p ℂ)).adjoint :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  apply @ext_inner_left ℂ _ _,
  intros a,
  rw [tensor_product.to_kronecker_apply, linear_map.adjoint_inner_right,
    kmul_representation a],
  simp_rw [map_sum, smul_hom_class.map_smul, sum_inner, inner_smul_left],
  repeat { apply finset.sum_congr rfl,
    intros, },
  symmetry,
  calc (star_ring_end ℂ) (a (x_1, x_3) (x_2, x_4)) *
    inner (std_basis_matrix x_1 x_2 1 ⊗ₖ std_basis_matrix x_3 x_4 1).kronecker_to_tensor_product
      (x ⊗ₜ[ℂ] y)
    = (star_ring_end ℂ) (a (x_1, x_3) (x_2, x_4)) *
      inner (std_basis_matrix x_1 x_2 1 ⊗ₜ[ℂ] std_basis_matrix x_3 x_4 1) (x ⊗ₜ[ℂ] y) :
  by rw kronecker_to_tensor_product_apply
  ... = (star_ring_end ℂ) (a (x_1, x_3) (x_2, x_4)) *
    (inner (std_basis_matrix x_1 x_2 1) x * inner (std_basis_matrix x_3 x_4 1) y) :
  by rw tensor_product.inner_tmul
  ... = (star_ring_end ℂ) (a (x_1, x_3) (x_2, x_4)) *
    inner (std_basis_matrix x_1 x_2 1 ⊗ₖ std_basis_matrix x_3 x_4 1) (x ⊗ₖ y) :
  by rw [module.dual.is_faithful_pos_map.inner_eq' (_ ⊗ₖ _),
    module.dual.tensor_mul_matrix, kronecker_conj_transpose, ← mul_kronecker_mul,
      ← mul_kronecker_mul, trace_kronecker, module.dual.is_faithful_pos_map.inner_eq',
      module.dual.is_faithful_pos_map.inner_eq']; refl,
end
lemma tensor_product.to_kronecker_adjoint [hφ : fact φ.is_faithful_pos_map] [hψ : fact ψ.is_faithful_pos_map] :
  (kronecker_to_tensor_product
    : (matrix (n × p) (n × p) ℂ) →ₗ[ℂ] (matrix n n ℂ ⊗[ℂ] matrix p p ℂ))
  = (@tensor_product.to_kronecker ℂ n p _ _ _ _ _ :
      (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) →ₗ[ℂ] matrix (n × p) (n × p) ℂ).adjoint :=
begin
  rw [@matrix.kronecker_to_tensor_product_adjoint n p _ _ _ _ φ ψ, linear_map.adjoint_adjoint],
end

lemma matrix.kronecker_to_tensor_product_comp_to_kronecker :
  (kronecker_to_tensor_product : matrix (n × p) (n × p) ℂ →ₗ[ℂ] _).comp
    (tensor_product.to_kronecker : matrix n n ℂ ⊗[ℂ] matrix p p ℂ →ₗ[ℂ] _)
  = 1 :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp_rw [linear_map.comp_apply, tensor_product.to_kronecker_to_tensor_product,
    linear_map.one_apply],
end

local notation `ℍ` := matrix n n ℂ
local notation `ℍ₂` := Π i, matrix (s i) (s i) ℂ
local notation `ℍ_`i := matrix (s i) (s i) ℂ
local notation `η` := algebra.linear_map ℂ ℍ
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `υ` :=
  ((tensor_product.assoc ℂ (matrix n n ℂ) (matrix n n ℂ) (matrix n n ℂ))
    : (matrix n n ℂ ⊗[ℂ] matrix n n ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ]
      matrix n n ℂ ⊗[ℂ] (matrix n n ℂ ⊗[ℂ] matrix n n ℂ))
local notation `υ⁻¹` :=
  ((tensor_product.assoc ℂ (matrix n n ℂ) (matrix n n ℂ) (matrix n n ℂ)).symm
    : matrix n n ℂ ⊗[ℂ] (matrix n n ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ]
      (matrix n n ℂ ⊗[ℂ] matrix n n ℂ ⊗[ℂ] matrix n n ℂ))
local notation `ϰ` := (↑(tensor_product.comm ℂ (matrix n n ℂ) ℂ)
  : (matrix n n ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] matrix n n ℂ))
local notation `ϰ⁻¹` := ((tensor_product.comm ℂ (matrix n n ℂ) ℂ).symm
  : (ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ] (matrix n n ℂ ⊗[ℂ] ℂ))
local notation `τ` := ((tensor_product.lid ℂ (matrix n n ℂ))
  : (ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ] matrix n n ℂ)
local notation `τ⁻¹` := ((tensor_product.lid ℂ (matrix n n ℂ)).symm
  : matrix n n ℂ →ₗ[ℂ] (ℂ ⊗[ℂ] matrix n n ℂ))
local notation `id` := (1 : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ)

lemma frobenius_equation [hφ : fact φ.is_faithful_pos_map] :
  (linear_map.mul' ℂ ℍ ⊗ₘ id) ∘ₗ υ⁻¹ ∘ₗ (id ⊗ₘ (linear_map.mul' ℂ ℍ).adjoint)
    = (linear_map.mul' ℂ ℍ).adjoint ∘ₗ linear_map.mul' ℂ ℍ :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp_rw [linear_map.comp_apply, tensor_product.map_tmul, linear_map.mul'_adjoint,
    tensor_product.tmul_sum, tensor_product.tmul_smul, map_sum, smul_hom_class.map_smul,
    linear_map.one_apply, linear_equiv.coe_coe, tensor_product.assoc_symm_tmul],
  simp only [tensor_product.map_tmul, linear_map.mul'_apply, linear_map.one_apply],
    -- kronecker_to_tensor_product_apply, linear_equiv.coe_to_linear_map,
    -- tensor_product.assoc_symm_tmul, linear_map.mul'_apply, linear_equiv.coe_coe],
  rw ← function.injective.eq_iff
    (kronecker_to_tensor : matrix (n × n) (n × n) ℂ ≃ₐ[ℂ] ℍ ⊗[ℂ] ℍ).symm.injective,
  simp_rw [map_sum, smul_hom_class.map_smul, kronecker_to_tensor, alg_equiv.symm_symm,
    tensor_to_kronecker, alg_equiv.coe_mk, tensor_product.to_kronecker_apply,
    ← matrix.ext_iff, matrix.sum_apply, pi.smul_apply, kronecker_map,
    of_apply, mul_eq_mul, mul_apply, std_basis_matrix, mul_boole, smul_ite,
    smul_zero, ite_and, finset.smul_sum, smul_ite, smul_zero],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq,
    finset.sum_ite_eq', finset.mem_univ, if_true],
  simp_rw [smul_eq_mul, mul_one, ← mul_apply, mul_rotate _ _ (x _ _), mul_assoc, ← finset.mul_sum,
    ← mul_apply, mul_comm _ ((x ⬝ y) _ _), eq_self_iff_true, forall_2_true_iff],
end

local notation `l(`x`)` := x →ₗ[ℂ] x

open_locale big_operators

noncomputable def matrix_direct_sum_from_to (i j : k) :
  -- {k : Type*} [decidable_eq k] {s : k → Type*}
  -- [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  -- (i j : k) :
  (matrix (s i) (s i) ℂ) →ₗ[ℂ] (matrix (s j) (s j) ℂ) :=
@direct_sum_from_to ℂ _ k _ (λ a, matrix (s a) (s a) ℂ) _ (λ a, matrix.module) i j

lemma matrix_direct_sum_from_to_same (i : k) :
  (matrix_direct_sum_from_to i i : matrix (s i) (s i) ℂ →ₗ[ℂ] _) = 1 :=
direct_sum_from_to_apply_same _

lemma linear_map.pi_mul'_apply_include_block' {i j : k} :
  (linear_map.mul' ℂ ℍ₂) ∘ₗ
    (tensor_product.map (include_block : (ℍ_ i) →ₗ[ℂ] ℍ₂) (include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂))
    = if (i = j) then ((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂)
      ∘ₗ (linear_map.mul' ℂ (ℍ_ j))
      ∘ₗ (tensor_product.map (matrix_direct_sum_from_to i j) (1 : (ℍ_ j) →ₗ[ℂ] (ℍ_ j)))) else 0 :=
begin
  rw [tensor_product.ext_iff],
  intros x y,
  ext1 a,
  simp only [linear_map.comp_apply, dite_apply, tensor_product.map_tmul, linear_map.mul'_apply,
    include_block_mul_same, finset.sum_apply, include_block_apply, finset.sum_dite_eq',
    finset.mem_univ, if_true, pi.mul_apply, dite_mul, mul_dite, mul_zero, zero_mul,
    ite_apply_lm, linear_map.zero_apply, ite_apply, pi.zero_apply, linear_map.one_apply],
  by_cases j = a,
  { simp_rw [matrix_direct_sum_from_to, direct_sum_from_to, linear_map.comp_apply],
    simp [pi.single, function.update, h],
    split_ifs; finish, },
  { simp [h], },
end

noncomputable def direct_sum_tensor_matrix :
  (Π i, matrix (s i) (s i) ℂ) ⊗[ℂ] (Π i, matrix (s i) (s i) ℂ)
    ≃ₗ[ℂ] Π i : k × k, (ℍ_ i.1) ⊗[ℂ] (ℍ_ i.2) :=
@direct_sum_tensor ℂ _ k k _ _ _ _ (λ i, matrix (s i) (s i) ℂ) (λ i, matrix (s i) (s i) ℂ) _ _
  (λ i, matrix.module) (λ i, matrix.module)

noncomputable def direct_sum_tensor_to_kronecker :
  ℍ₂ ⊗[ℂ] ℍ₂ ≃ₗ[ℂ] Π i : (k × k), matrix (s i.fst × s i.snd) (s i.fst × s i.snd) ℂ :=
{ to_fun := λ x i, (direct_sum_tensor_matrix x i).to_kronecker,
  inv_fun := λ x, direct_sum_tensor_matrix.symm
    (λ i, (x i).kronecker_to_tensor_product),
  left_inv := λ x, by { simp only [tensor_product.to_kronecker_to_tensor_product,
    linear_equiv.symm_apply_apply], },
  right_inv := λ x, by { simp only [linear_equiv.apply_symm_apply,
    kronecker_to_tensor_product_to_kronecker], },
  map_add' := λ x y, by { simp only [map_add, pi.add_apply], refl, },
  map_smul' := λ r x, by { simp only [smul_hom_class.map_smul, pi.smul_apply, ring_hom.id_apply],
    refl, } }

lemma frobenius_equation_direct_sum_aux [hθ : Π i, fact (θ i).is_faithful_pos_map]
  (x y : ℍ₂) (i j : k) :
  ((linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
    ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
      ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
        (include_block (x i) ⊗ₜ[ℂ] include_block (y j))
  =
    if (i = j) then (
      ((include_block ⊗ₘ include_block) ∘ₗ
        ((linear_map.mul' ℂ (ℍ_ j)).adjoint ∘ₗ (linear_map.mul' ℂ (ℍ_ j))))
        (x j ⊗ₜ[ℂ] y j)) else 0 :=
begin
  have := calc
  ((linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
    ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
      ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
        (include_block (x i) ⊗ₜ[ℂ] include_block (y j))
    =
    (linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
      ((tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
      ((include_block ⊗ₘ (include_block ⊗ₘ include_block))
      (x i ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint (y j)))) : _
  ... = (linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
      (((include_block ⊗ₘ include_block) ⊗ₘ include_block)
      ((tensor_product.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm
      (x i ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint (y j)))) : _
  ... = if (i = j) then (
      (((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂) ⊗ₘ include_block) ∘ₗ
      ((linear_map.mul' ℂ (ℍ_ j) ⊗ₘ (1 : l(ℍ_ j)))
       ∘ₗ ↑(tensor_product.assoc ℂ (ℍ_ j) (ℍ_ j) (ℍ_ j)).symm
       ∘ₗ ((1 : l(ℍ_ j)) ⊗ₘ (linear_map.mul' ℂ (ℍ_ j)).adjoint)))
        (x j ⊗ₜ[ℂ] y j)) else 0 : _,
  { simp only [this, @frobenius_equation (s j)], },
  { simp only [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.map_tmul,
      linear_map.one_apply, linear_map.pi_mul'_adjoint_single_block], },
  { congr,
    simp_rw [← linear_equiv.coe_coe, ← linear_map.comp_apply,
      tensor_product.assoc_include_block], },
  { simp_rw [← linear_map.comp_apply, ← tensor_product.map_comp,
      linear_map.pi_mul'_apply_include_block', linear_map.comp_apply,
      tensor_product.ite_map, ite_apply_lm, tensor_product.zero_map, linear_map.zero_apply,
      tensor_product.map_tmul, linear_equiv.coe_coe, linear_map.one_apply],
    obtain ⟨α,β,hαβ⟩ := tensor_product.eq_span ((linear_map.mul' ℂ (ℍ_ j)).adjoint (y j)),
    rw [← hαβ],
    simp only [tensor_product.tmul_sum, map_sum, tensor_product.assoc_symm_tmul,
      tensor_product.map_tmul, linear_map.comp_apply,
      linear_map.one_apply],
    split_ifs,
    { apply finset.sum_congr rfl,
      intros,
      rw [h, matrix_direct_sum_from_to, direct_sum_from_to_apply_same, linear_map.one_apply], },
    { refl, }, },
end

lemma direct_sum_tensor_to_kronecker_apply
  (x y : ℍ₂) (r : k × k) (a b : s r.1 × s r.2) :
  (direct_sum_tensor_to_kronecker (x ⊗ₜ[ℂ] y))
  r a b
  = x r.1 a.1 b.1 * y r.2 a.2 b.2 :=
begin
  simp_rw [direct_sum_tensor_to_kronecker,
    linear_equiv.coe_mk, direct_sum_tensor_matrix, direct_sum_tensor_apply,
    tensor_product.to_kronecker_apply, kronecker_map, of_apply],
end

-- lemma pi_frobenius_equation [hθ : Π i, fact (θ i).is_faithful_pos_map] :
--   ((linear_map.mul' ℂ ℍ₂  ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--     = (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ (linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂)) :=
-- begin
--   apply tensor_product.ext',
--   intros x y,
--   rw [← sum_include_block x, ← sum_include_block y],
--   calc
--   ((linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--         ((∑ i, include_block (x i)) ⊗ₜ[ℂ] (∑ j, include_block (y j)))
--   =
--   ∑ i j, if (i = j) then (
--       ((include_block ⊗ₘ include_block) ∘ₗ
--         ((linear_map.mul' ℂ (ℍ_ j)).adjoint ∘ₗ (linear_map.mul' ℂ (ℍ_ j))))
--         ((x j) ⊗ₜ[ℂ] (y j))) else 0 :
--   by { simp_rw [tensor_product.sum_tmul, tensor_product.tmul_sum, map_sum],
--     repeat { apply finset.sum_congr rfl, intros },
--     rw [frobenius_equation_direct_sum_aux], }
--   ... =
--   ∑ j, ((include_block ⊗ₘ include_block)
--       ((linear_map.mul' ℂ (ℍ_ j)).adjoint
--       ((linear_map.mul' ℂ (ℍ_ j))
--       ((x j) ⊗ₜ[ℂ] (y j))))) :
--   by { simp_rw [finset.sum_ite_eq, finset.mem_univ, if_true,
--     linear_map.comp_apply], }
--   ... =
--   ∑ j, (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂)
--     ∘ₗ (include_block ∘ₗ (linear_map.mul' ℂ (ℍ_ j))))
--       ((x j) ⊗ₜ[ℂ] (y j)) :
--   by { simp_rw [linear_map.comp_apply, linear_map.pi_mul'_adjoint_single_block], }
--   ... =
--   ∑ i j, ite (i = j)
--   ((((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ
--   (include_block.comp ((linear_map.mul' ℂ (matrix (s j) (s j) ℂ)).comp (matrix_direct_sum_from_to i j ⊗ₘ 1))))
--      (x i ⊗ₜ[ℂ] y j)
--   )
--    0 :
--   by { simp_rw [finset.sum_ite_eq, finset.mem_univ, if_true,
--     matrix_direct_sum_from_to_same, tensor_product.map_one, linear_map.comp_one], }
--   ... =
--   ∑ j, (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂)
--     ((linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂)
--      (include_block (x j) ⊗ₜ[ℂ] include_block (y j)))) :
--   by { simp_rw [← linear_map.pi_mul'_apply_include_block'], }
--   ... =
--   (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ (linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂))
--   ((∑ i, include_block (x i)) ⊗ₜ[ℂ] (∑ j, include_block (y j))) :
--   by {  },

-- end

lemma frobenius_equation' [hφ : fact φ.is_faithful_pos_map] :
  (id ⊗ₘ linear_map.mul' ℂ ℍ) ∘ₗ υ ∘ₗ ((linear_map.mul' ℂ ℍ).adjoint ⊗ₘ id)
    = (linear_map.mul' ℂ ℍ).adjoint ∘ₗ linear_map.mul' ℂ ℍ :=
begin
  have := @frobenius_equation n _ _ φ _,
  apply_fun linear_map.adjoint at this,
  simp_rw [linear_map.adjoint_comp, tensor_product.map_adjoint,
    linear_map.adjoint_adjoint, tensor_product.assoc_symm_adjoint, ← linear_map.star_eq_adjoint,
    star_one, linear_map.comp_assoc] at this,
  exact this,
end

lemma linear_map.mul'_assoc :
  (linear_map.mul' ℂ (matrix n n ℂ)) ∘ₗ (linear_map.mul' ℂ (matrix n n ℂ) ⊗ₘ id)
    = linear_map.mul' ℂ (matrix n n ℂ) ∘ₗ (id ⊗ₘ linear_map.mul' ℂ (matrix n n ℂ))
      ∘ₗ (↑(tensor_product.assoc ℂ (matrix n n ℂ) (matrix n n ℂ) (matrix n n ℂ) : _ ≃ₗ[ℂ] _) : _ →ₗ[ℂ] _) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  simp only [linear_map.comp_apply, tensor_product.map_tmul, linear_map.mul'_apply,
    linear_map.one_apply, linear_equiv.coe_coe, tensor_product.assoc_tmul, mul_assoc],
end
lemma linear_map.mul'_coassoc [hφ : fact φ.is_faithful_pos_map] :
  ((linear_map.mul' ℂ ℍ).adjoint ⊗ₘ id) ∘ₗ (linear_map.mul' ℂ ℍ).adjoint
    = υ⁻¹ ∘ₗ (id ⊗ₘ (linear_map.mul' ℂ ℍ).adjoint) ∘ₗ (linear_map.mul' ℂ ℍ).adjoint :=
begin
  have := @linear_map.mul'_assoc n _ _,
  apply_fun linear_map.adjoint at this,
  simp_rw [linear_map.adjoint_comp, tensor_product.map_adjoint,
    tensor_product.assoc_adjoint, ← linear_map.star_eq_adjoint, star_one,
    linear_map.comp_assoc] at this,
  exact this,
end

--  m(η ⊗ id) = τ
lemma linear_map.mul'_comp_unit_map_id_eq_lid :
  linear_map.mul' ℂ ℍ ∘ₗ (η ⊗ₘ id) = τ :=
begin
  rw tensor_product.ext_iff,
  intros α x,
  simp_rw [linear_map.comp_apply, tensor_product.map_tmul, algebra.linear_map_apply,
    algebra.algebra_map_eq_smul_one, linear_map.mul'_apply,
    linear_equiv.coe_coe, tensor_product.lid_tmul, linear_map.one_apply, smul_mul_assoc, one_mul],
end

-- m(id ⊗ η)κ⁻¹ = τ
lemma linear_map.mul'_comp_id_map_unit_assoc_eq_lid :
  linear_map.mul' ℂ ℍ ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ = τ :=
begin
  rw tensor_product.ext_iff,
  intros α x,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.comm_symm_tmul,
    tensor_product.map_tmul,  algebra.linear_map_apply,
    algebra.algebra_map_eq_smul_one,
    linear_map.one_apply, linear_map.mul'_apply,
    tensor_product.lid_tmul, mul_smul_one],
end

private lemma linear_map.id_map_mul'_comp_unit_eq
  [hφ : fact φ.is_faithful_pos_map] :
  (id ⊗ₘ ((linear_map.mul' ℂ ℍ).adjoint ∘ₗ η))
    = (id ⊗ₘ (linear_map.mul' ℂ ℍ).adjoint) ∘ₗ (id ⊗ₘ η) :=
begin
  rw [← tensor_product.map_comp, linear_map.comp_one],
end

-- (m ⊗ id)υ⁻¹(id ⊗ m⋆η)κ⁻¹τ⁻¹ = m⋆
lemma linear_map.mul'_adjoint_eq' [hφ : fact φ.is_faithful_pos_map] :
  (linear_map.mul' ℂ ℍ ⊗ₘ id) ∘ₗ υ⁻¹ ∘ₗ (id ⊗ₘ ((linear_map.mul' ℂ ℍ).adjoint ∘ₗ η)) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
    = (linear_map.mul' ℂ ℍ).adjoint :=
begin
  rw linear_map.id_map_mul'_comp_unit_eq,
  have := @frobenius_equation n _ _ φ _,
  simp_rw [← linear_map.comp_assoc] at this ⊢,
  rw [this],
  simp_rw [linear_map.comp_assoc, ← linear_map.comp_assoc _ ϰ⁻¹,
    ← linear_map.comp_assoc _ (_ ∘ₗ ϰ⁻¹), linear_map.mul'_comp_id_map_unit_assoc_eq_lid,
    linear_equiv.comp_coe, linear_equiv.symm_trans_self, linear_equiv.refl_to_linear_map,
    linear_map.comp_id],
end

private lemma linear_map.mul'_comp_unit_map_id_eq [hφ : fact φ.is_faithful_pos_map] :
  (((linear_map.mul' ℂ ℍ).adjoint ∘ₗ η) ⊗ₘ id)
    = ((linear_map.mul' ℂ ℍ).adjoint ⊗ₘ id) ∘ₗ (η ⊗ₘ id) :=
begin
  rw [← tensor_product.map_comp, linear_map.comp_one],
end

-- (id ⊗ m)υ(m∗η ⊗ id) τ⁻¹ = m⋆
lemma linear_map.mul'_adjoint_eq'' [hφ : fact φ.is_faithful_pos_map] :
  (id ⊗ₘ linear_map.mul' ℂ ℍ) ∘ₗ υ ∘ₗ (((linear_map.mul' ℂ ℍ).adjoint ∘ₗ η) ⊗ₘ id) ∘ₗ τ⁻¹
    = (linear_map.mul' ℂ ℍ).adjoint :=
begin
  rw linear_map.mul'_comp_unit_map_id_eq,
  have := @frobenius_equation' n _ _ φ _,
  simp_rw [← linear_map.comp_assoc] at this ⊢,
  rw [this],
  simp_rw [linear_map.comp_assoc, ← linear_map.comp_assoc _ (_ ⊗ₘ _),
    linear_map.mul'_comp_unit_map_id_eq_lid, linear_equiv.comp_coe,
    linear_equiv.symm_trans_self, linear_equiv.refl_to_linear_map,
    linear_map.comp_id],
end
