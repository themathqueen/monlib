/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.tensor_hilbert
import linear_algebra.my_ips.nontracial

/-!
 # Frobenius equations

 This file contains the proof of the Frobenius equations.
-/

variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]
  {φ : matrix n n ℂ →ₗ[ℂ] ℂ} (hφ : φ.is_faithful_pos_map)
  {ψ : matrix p p ℂ →ₗ[ℂ] ℂ} (hψ : ψ.is_faithful_pos_map)
  {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {θ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}
  [hθ : Π i, fact (θ i).is_faithful_pos_map]

open_locale matrix kronecker tensor_product big_operators functional
open matrix

-- def linear_map.is_faithful_pos_map.tensor_pow (x : ℕ) :
--   ⨂[ℂ]^x (matrix n n ℂ) →ₗ[ℂ] ℂ :=
-- { to_fun := λ a, by { simp only [tensor_algebra] } }
noncomputable def linear_map.tensor_mul (φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ) (φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ) :
  (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) →ₗ[ℂ] ℂ :=
((tensor_product.lid ℂ ℂ) : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ∘ₗ (tensor_product.map φ₁ φ₂)

lemma linear_map.tensor_mul_apply (φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ)
  (φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ) (x : matrix n n ℂ) (y : matrix p p ℂ) :
  (φ₁.tensor_mul φ₂) (x ⊗ₜ[ℂ] y) = φ₁ x * φ₂ y :=
rfl
lemma linear_map.tensor_mul_apply' (φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ) (φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ)
  (x : matrix n n ℂ ⊗[ℂ] matrix p p ℂ) :
  φ₁.tensor_mul φ₂ x = ∑ i j k l, (x.to_kronecker (i,k) (j,l))
    * (φ₁ (std_basis_matrix i j (1 : ℂ)) * φ₂ (std_basis_matrix k l (1 : ℂ))) :=
begin
  simp_rw [← linear_map.tensor_mul_apply, ← smul_eq_mul, ← smul_hom_class.map_smul, ← map_sum],
  rw ← x.matrix_eq_sum_std_basis,
end

lemma linear_map.tensor_mul_apply'' (φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ) (φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ)
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
    linear_map.tensor_mul_apply, linear_map.mul_left_apply, trace_linear_map_apply,
    mul_eq_mul, ← mul_kronecker_mul, trace_kronecker, linear_map.linear_functional_eq'],
end

lemma linear_map.tensor_mul_matrix (φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ) (φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ) :
  ((φ₁.tensor_mul φ₂).comp kronecker_to_tensor_product).matrix = φ₁.matrix ⊗ₖ φ₂.matrix :=
begin
  symmetry,
  apply linear_map.linear_functional_eq_of,
  simp_rw [← linear_map.tensor_mul_apply'' φ₁ φ₂],
  intros,
  refl,
end

@[instance] def linear_map.is_faithful_pos_map.tensor_mul
  {φ₁ : matrix n n ℂ →ₗ[ℂ] ℂ}
  {φ₂ : matrix p p ℂ →ₗ[ℂ] ℂ} [hφ₁ : fact φ₁.is_faithful_pos_map]
  [hφ₂ : fact φ₂.is_faithful_pos_map] :
  fact ((φ₁.tensor_mul φ₂).comp kronecker_to_tensor_product).is_faithful_pos_map :=
begin
  apply fact.mk,
  rw [linear_map.is_faithful_pos_map_iff_of_matrix, linear_map.tensor_mul_matrix],
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
  by rw [linear_map.is_faithful_pos_map.inner_eq' (_ ⊗ₖ _),
    linear_map.tensor_mul_matrix, kronecker_conj_transpose, ← mul_kronecker_mul,
      ← mul_kronecker_mul, trace_kronecker, linear_map.is_faithful_pos_map.inner_eq',
      linear_map.is_faithful_pos_map.inner_eq']; refl,
end
lemma tensor_product.to_kronecker_adjoint [hφ : fact φ.is_faithful_pos_map] [hψ : fact ψ.is_faithful_pos_map] :
  (kronecker_to_tensor_product
    : (matrix (n × p) (n × p) ℂ) →ₗ[ℂ] (matrix n n ℂ ⊗[ℂ] matrix p p ℂ))
  = (@tensor_product.to_kronecker ℂ n p _ _ _ _ _ :
      (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) →ₗ[ℂ] matrix (n × p) (n × p) ℂ).adjoint :=
begin
  rw [@matrix.kronecker_to_tensor_product_adjoint n p _ _ _ _ φ ψ, linear_map.adjoint_adjoint],
end


lemma kronecker_to_tensor_to_linear_map_eq :
  (kronecker_to_tensor : matrix (n × p) (n × p) ℂ ≃ₐ[ℂ] _).to_linear_map
    = (kronecker_to_tensor_product
      : matrix (n × p) (n × p) ℂ →ₗ[ℂ] matrix n n ℂ ⊗[ℂ] matrix p p ℂ) :=
rfl
lemma tensor_to_kronecker_to_linear_map_eq :
  (tensor_to_kronecker
    : (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) ≃ₐ[ℂ] matrix (n × p) (n × p) ℂ).to_linear_map
  = (tensor_product.to_kronecker
    : (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) →ₗ[ℂ] matrix (n × p) (n × p) ℂ) :=
rfl

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

def direct_sum_from_to {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] (i j : ι₁) :
  (M₁ i) →ₗ[R] (M₁ j) :=
(linear_map.proj j) ∘ₗ (linear_map.single i)

lemma direct_sum_from_to_apply_same {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] (i : ι₁) :
  direct_sum_from_to i i = (1 : M₁ i →ₗ[R] M₁ i) :=
begin
  ext1 x,
  simp only [direct_sum_from_to, linear_map.comp_apply, linear_map.coe_single, pi.single,
    linear_map.coe_proj, function.eval_apply, function.update_apply, pi.zero_apply,
    ite_apply_lm, linear_map.zero_apply, linear_map.one_apply],
  simp,
end
lemma direct_sum_from_to_apply_ne_same {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] {i j : ι₁} (h : j ≠ i) :
  direct_sum_from_to i j = (0 : M₁ i →ₗ[R] M₁ j) :=
begin
  ext1 x,
  simp only [direct_sum_from_to, linear_map.comp_apply, linear_map.coe_single, pi.single,
    linear_map.coe_proj, function.eval_apply, function.update_apply, pi.zero_apply,
    ite_apply_lm, linear_map.zero_apply, linear_map.one_apply],
  simp [h],
end

noncomputable def matrix_direct_sum_from_to (i j : k) :
  (ℍ_ i) →ₗ[ℂ] (ℍ_ j) :=
@direct_sum_from_to ℂ _ k _ (λ a, ℍ_ a) _ (λ a, matrix.module) i j


lemma linear_map.mul'_direct_sum_apply_include_block' {i j : k} :
  (linear_map.mul' ℂ ℍ₂) ∘ₗ
    (tensor_product.map (include_block : (ℍ_ i) →ₗ[ℂ] ℍ₂) (include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂))
    = if (i = j) then ((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂)
      ∘ₗ (linear_map.mul' ℂ (ℍ_ j))
      ∘ₗ ((matrix_direct_sum_from_to i j) ⊗ₘ 1)) else 0 :=
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

lemma direct_sum.tensor_coe_zero {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  ⇑(0 : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = 0 :=
rfl
lemma direct_sum.tensor_coe_add {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x y : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) :
  ⇑(x + y : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = x + y :=
rfl
lemma direct_sum.tensor_coe_smul {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) (r : R) :
  ⇑(r • x : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = r • x :=
rfl

def pi.tensor_of {R : Type*} [comm_semiring R] {ι₁ ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (i : ι₁ × ι₂) :
  M₁ i.fst ⊗[R] M₂ i.snd →ₗ[R] (Π j, M₁ j) ⊗[R] (Π j, M₂ j) :=
(@linear_map.single R ι₁ _ M₁ _ _ _ i.fst ⊗ₘ @linear_map.single R ι₂ _ M₂ _ _ _ i.snd)

def pi.tensor_proj {R : Type*} [comm_semiring R] {ι₁ ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (i : ι₁ × ι₂) :
  (Π j, M₁ j) ⊗[R] (Π j, M₂ j) →ₗ[R] M₁ i.fst ⊗[R] M₂ i.snd :=
(@linear_map.proj R ι₁ _ M₁ _ _ i.fst ⊗ₘ @linear_map.proj R ι₂ _ M₂ _ _ i.snd)

def direct_sum_tensor_to_fun
  {R : Type*} [comm_semiring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i, M₁ i) ⊗[R] (Π i, M₂ i) →ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd :=
{ to_fun :=  λ x i, (pi.tensor_proj i x),
  map_add' := λ x y,
    by { simp only [map_add, direct_sum.tensor_coe_add],
      refl, },
  map_smul' := λ r x,
    by { simp only [smul_hom_class.map_smul, direct_sum.tensor_coe_smul, ring_hom.id_apply],
      refl, } }

lemma direct_sum_tensor_to_fun_apply
  {R : Type*} [comm_semiring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : Π i, M₁ i) (y : Π i, M₂ i) (i : ι₁ × ι₂) :
  direct_sum_tensor_to_fun (x ⊗ₜ[R] y) i = x i.1 ⊗ₜ[R] y i.2 :=
rfl

def direct_sum_tensor_inv_fun {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd) →ₗ[R] ((Π i, M₁ i) ⊗[R] (Π i, M₂ i)) :=
{ to_fun :=  λ x, (∑ i : ι₁ × ι₂, pi.tensor_of i (x i)),
  map_add' := λ x y, by { simp only [map_add, pi.add_apply, finset.sum_add_distrib], },
  map_smul' := λ r x, by { simp only [smul_hom_class.map_smul, pi.smul_apply, ring_hom.id_apply],
    rw [← finset.smul_sum], } }

lemma function.sum_update_eq_self {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  [fintype ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] (x : Π i, M₁ i) :
  ∑ (x_1 : ι₁), function.update 0 x_1 (x x_1) = x :=
begin
  ext,
  simp only [finset.sum_apply, function.update, finset.sum_dite_eq, finset.mem_univ, if_true,
    pi.zero_apply],
end

lemma direct_sum_tensor_inv_fun_apply_to_fun
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : (Π i, M₁ i) ⊗[R] Π i, M₂ i) :
  direct_sum_tensor_inv_fun (direct_sum_tensor_to_fun x) = x :=
begin
  apply x.induction_on,
  { simp only [map_zero], },
  { intros x y,
    simp only [direct_sum_tensor_inv_fun, linear_map.coe_mk, linear_map.comp_apply,
      direct_sum_tensor_to_fun_apply],
    calc ∑ (i : ι₁ × ι₂), (pi.tensor_of i) (x i.fst ⊗ₜ[R] y i.snd)
      = ∑ (i : ι₁) (j : ι₂), (pi.tensor_of (i,j)) (x i ⊗ₜ[R] y j) :
    by { rw ← finset.sum_product',
      simp only [finset.univ_product_univ],
      apply finset.sum_congr rfl,
      intros,
      refl, }
    ... = ∑ (x_1 : ι₁) (x_2 : ι₂), function.update 0 (x_1, x_2).fst (x x_1) ⊗ₜ[R] function.update 0 (x_1, x_2).snd (y x_2) :
    by { simp only [pi.tensor_of, tensor_product.map_tmul],
      refl, }
    ... = ∑ (x_1 : ι₁) (x_2 : ι₂), function.update 0 x_1 (x x_1) ⊗ₜ[R] function.update 0 x_2 (y x_2) : rfl
    ... = (∑ (x_1 : ι₁), function.update 0 x_1 (x x_1)) ⊗ₜ[R]
      (∑ (x_2 : ι₂), function.update 0 x_2 (y x_2)) :
    by { simp only [tensor_product.tmul_sum, tensor_product.sum_tmul], }
    ... = x ⊗ₜ[R] y : _,
    congr;
    exact @function.sum_update_eq_self R _ _ _ _ _ _ _ _, },
  { intros x y hx hy,
    simp only [map_add, hx, hy], },
end

lemma pi.tensor_proj_apply_pi_tensor_of
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (i j : ι₁ × ι₂) (x : Π i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
  (pi.tensor_proj i) (pi.tensor_of j (x j)) = ite (i = j) (x i) 0 :=
begin
  have t1 : ∀ i j : ι₁, (linear_map.proj j).comp (linear_map.single i) = (direct_sum_from_to i j : M₁ i →ₗ[R] M₁ j)
  := λ i j, rfl,
  have t2 : ∀ i j : ι₂, (linear_map.proj j).comp (linear_map.single i) = (direct_sum_from_to i j : M₂ i →ₗ[R] M₂ j)
  := λ i j, rfl,
  simp only [pi.tensor_of, pi.tensor_proj, ← linear_map.comp_apply, ← tensor_product.map_comp,
    t1, t2],
  split_ifs,
  { rw h,
    simp only [direct_sum_from_to_apply_same, tensor_product.map_one, linear_map.one_apply], },
  { rw [prod.eq_iff_fst_eq_snd_eq, not_and_distrib] at h,
    rcases h with (h|h),
    { rw [direct_sum_from_to_apply_ne_same h, tensor_product.zero_map, linear_map.zero_apply], },
    { rw [direct_sum_from_to_apply_ne_same h, tensor_product.map_zero, linear_map.zero_apply], }, },
end

lemma direct_sum_tensor_to_fun_apply_inv_fun {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x : Π i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
  direct_sum_tensor_to_fun (direct_sum_tensor_inv_fun x) = x :=
begin
  simp only [direct_sum_tensor_to_fun, direct_sum_tensor_inv_fun, linear_map.coe_mk,
    map_sum, pi.tensor_proj_apply_pi_tensor_of],
  ext1,
  simp only [finset.sum_apply, finset.sum_ite_eq, finset.mem_univ, if_true],
end

def direct_sum_tensor
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i, M₁ i) ⊗[R] (Π i, M₂ i) ≃ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd :=
{ to_fun := direct_sum_tensor_to_fun,
  inv_fun := direct_sum_tensor_inv_fun,
  left_inv := λ x, direct_sum_tensor_inv_fun_apply_to_fun x,
  right_inv := λ x, direct_sum_tensor_to_fun_apply_inv_fun x,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ r x, smul_hom_class.map_smul _ _ _ }

lemma direct_sum_tensor_apply
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : (Π i, M₁ i)) (y : (Π i, M₂ i)) (i : ι₁ × ι₂) :
  direct_sum_tensor (x ⊗ₜ[R] y) i = x i.1 ⊗ₜ[R] y i.2 :=
rfl

@[ext] lemma pi.tensor_ext_iff
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x z : (Π i, M₁ i)) (y w : (Π i, M₂ i)) :
  x ⊗ₜ[R] y = z ⊗ₜ[R] w ↔ ∀ i j, x i ⊗ₜ[R] y j = z i ⊗ₜ[R] w j :=
begin
  rw ← function.injective.eq_iff (direct_sum_tensor : (Π i, M₁ i) ⊗[R] (Π i, M₂ i) ≃ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd).injective,
  simp_rw [function.funext_iff, direct_sum_tensor_apply, prod.forall],
end

noncomputable def direct_sum_tensor_matrix :
  ℍ₂ ⊗[ℂ] ℍ₂ ≃ₗ[ℂ] Π i : k × k, (ℍ_ i.fst) ⊗[ℂ] (ℍ_ i.snd) :=
@direct_sum_tensor ℂ _ k k _ _ _ _ (λ i, ℍ_ i) (λ i, ℍ_ i) _ _
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

lemma include_block_mul_include_block {i j : k} (x : ℍ_ i) (y : ℍ_ j) :
  (include_block x) * (include_block y) =
    dite (j = i) (λ h, include_block (x * (by { rw ← h, exact y, }))) (λ h, 0) :=
begin
  ext1,
  simp [include_block, dite_mul, mul_dite, mul_zero, zero_mul, dite_apply, pi.zero_apply],
  split_ifs; finish,
end

lemma tensor_product.assoc_include_block {i j : k} :
  ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm ∘ₗ
    ((include_block : (ℍ_ i) →ₗ[ℂ] ℍ₂)
      ⊗ₘ ((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂) ⊗ₘ (include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂)))
  =
   (((include_block : (ℍ_ i) →ₗ[ℂ] ℍ₂)
      ⊗ₘ ((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂))) ⊗ₘ (include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂)) ∘ₗ
    ↑(tensor_product.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm :=
begin
  apply tensor_product.ext_threefold',
  intros x y z,
  simp only [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.assoc_symm_tmul,
    tensor_product.map_tmul],
end

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
      linear_map.one_apply, linear_map.mul'_adjoint_single_block], },
  { congr,
    simp_rw [← linear_equiv.coe_coe, ← linear_map.comp_apply,
      tensor_product.assoc_include_block], },
  { simp_rw [← linear_map.comp_apply, ← tensor_product.map_comp,
      linear_map.mul'_direct_sum_apply_include_block', linear_map.comp_apply,
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

-- lemma frobenius_equation_direct_sum {i j : k} (x y : ℍ₂) :
--   ((M ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ (M⋆ : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--         (include_block (x i) ⊗ₜ[ℂ] include_block (y j))
--     = ((M⋆ : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ (M : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂))
--       (include_block (x i) ⊗ₜ[ℂ] include_block (y j)) :=
-- begin
--   letI := λ a, (hθ a).normed_add_comm_group,
--   letI := λ a, (hθ a).inner_product_space,
--   have := calc
--   ((M ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ (M⋆ : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--         (include_block (x i) ⊗ₜ[ℂ] include_block (y j))
--     =
--     (M ⊗ₘ (1 : l(ℍ₂)))
--       ((tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ((include_block ⊗ₘ (include_block ⊗ₘ include_block))
--       (x i ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint (y j)))) : _
--   ... = (M ⊗ₘ (1 : l(ℍ₂)))
--       (((include_block ⊗ₘ include_block) ⊗ₘ include_block)
--       ((tensor_product.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm
--       (x i ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint (y j)))) : _
--   ... = if (i = j) then (
--       (((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂) ⊗ₘ include_block) ∘ₗ
--       ((linear_map.mul' ℂ (ℍ_ j) ⊗ₘ (1 : l(ℍ_ j)))
--        ∘ₗ ↑(tensor_product.assoc ℂ (ℍ_ j) (ℍ_ j) (ℍ_ j)).symm
--        ∘ₗ ((1 : l(ℍ_ j)) ⊗ₘ (linear_map.mul' ℂ (ℍ_ j)).adjoint)))
--         (x j ⊗ₜ[ℂ] y j)) else 0 : _,
--   -- ... = if (i = j) then (
--   --     ((include_block ⊗ₘ include_block) ∘ₗ
--   --       ((linear_map.mul' ℂ (ℍ_ j)).adjoint ∘ₗ (linear_map.mul' ℂ (ℍ_ j)))) (x j ⊗ₜ[ℂ] y j)) else 0 : _,
--   -- ... = if (i = j) then (
--   --     (include_block ⊗ₘ include_block)
--   --     ((linear_map.mul' ℂ (ℍ_ j)).adjoint
--   --     ((linear_map.mul' ℂ (ℍ_ j)) (x j ⊗ₜ[ℂ] y j)))) else 0 : _,
--   { rw this,
--     simp_rw [frobenius_equation (hθ j)],
--    }
--   -- ... = (M ⊗ₘ (1 : l(ℍ₂)))
--   --     (((include_block ⊗ₘ include_block) ⊗ₘ include_block)
--   --     ((tensor_product.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm
--   --     (x ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint y))) : _
--   -- ... = (M ∘ₗ (include_block ⊗ₘ include_block) ⊗ₘ include_block)
--   --     ((tensor_product.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm
--   --     (x ⊗ₜ[ℂ] (linear_map.mul' ℂ (ℍ_ j)).adjoint y)) : _
--   -- ... = 0 : _,
--   -- rw ← (direct_sum_tensor_to_kronecker : ℍ₂ ⊗[ℂ] ℍ₂ ≃ₗ[ℂ] Π i : (k × k), matrix (s i.fst × s i.snd) (s i.fst × s i.snd) ℂ).injective.eq_iff,
--   -- ext1 a,
--   -- ext1 b c,
--   -- simp_rw [linear_map.comp_apply, tensor_product.map_tmul, linear_map.mul'_adjoint_single_block,
--   --   linear_map.mul'_adjoint, map_sum, smul_hom_class.map_smul, tensor_product.tmul_sum,
--   --   tensor_product.tmul_smul, map_sum, smul_hom_class.map_smul, linear_equiv.coe_coe,
--   --   tensor_product.map_tmul, tensor_product.assoc_symm_tmul, tensor_product.map_tmul,
--   --   linear_map.one_apply, linear_map.mul'_apply, include_block_mul_include_block,
--   --   direct_sum_tensor_to_kronecker, linear_equiv.coe_mk, direct_sum_tensor_matrix,
--   --   direct_sum_tensor_apply, tensor_product.to_kronecker_apply,
--   --   finset.sum_apply, pi.smul_apply, kronecker_map, of_apply,
--   --   dite_apply, dite_mul, pi.zero_apply, zero_mul, smul_dite, smul_zero,include_block_apply_std_basis_matrix, include_block_apply,
--   --   block_diag'_apply, dite_apply, dite_mul, pi.zero_apply, zero_mul,
--   --   linear_map.apply_dite, map_zero, direct_sum_tensor, linear_equiv.coe_mk,
--   --   linear_map.apply_dite, dite_apply, map_zero, pi.zero_apply, linear_map.apply_dite,
--   --   map_zero, dite_apply, pi.zero_apply, finset.sum_dite_irrel, finset.sum_const_zero],
--   -- congr,
--   -- ext1 h,
--   -- simp only [h, linear_map.mul'_adjoint_single_block, smul_dite, smul_zero,
--   --   finset.sum_dite_irrel, finset.sum_const_zero, std_basis_matrix],
--   -- by_cases j = i,
--   -- { simp only [h, eq_self_iff_true, dif_pos, linear_map.mul'_adjoint_single_block,
--   --     linear_map.mul'_adjoint, map_sum, smul_hom_class.map_smul, pi.smul_apply,
--   --     finset.sum_apply, tensor_product.map_tmul, direct_sum_tensor_apply,
--   --     tensor_product.to_kronecker_apply, kronecker_map, of_apply,
--   --     include_block_apply_std_basis_matrix],
--   --   simp only [std_basis_matrix, block_diag'_apply, mul_ite, mul_one, mul_zero,
--   --     ite_mul, one_mul, zero_mul, smul_ite, smul_zero, smul_dite, mul_dite, dite_mul],
--   --   simp only [finset.sum_dite_irrel, finset.sum_const_zero, finset.sum_ite_irrel,
--   --     ite_and, sigma.mk.inj_iff, finset.sum_ite_eq', finset.sum_ite_eq, finset.sum_dite_eq,
--   --     finset.sum_dite_eq', finset.mem_univ, if_true],
--   --   split_ifs; simp [h_1, h],
--   --   apply finset.sum_congr rfl,
--   --   intros h_2,
--   --   split_ifs;
--   --   simp [h_3], }

--   -- rw [matrix_eq_sum_include_block x, matrix_eq_sum_include_block y],
--   -- simp only [tensor_product.sum_tmul, tensor_product.tmul_sum, map_sum,
--   -- simp_rw [← linear_map.comp_apply, ← tensor_product.map_tmul, linear_map.mul'_adjoint_single_block hθ],
--   --   linear_map.one_apply],
--   -- simp_rw [← tensor_product.map_tmul, ← linear_map.comp_apply,
--   --   ← linear_equiv.to_linear_map_eq_coe, tensor_product.assoc_symm_comp_map,
--   --   ← linear_map.comp_assoc, ← tensor_product.map_comp],

--   -- have := calc ∑ (x_1 x_2 : k), ((((linear_map.mul' ℂ ℍ₂).comp (include_block ⊗ₘ include_block)) ⊗ₘ include_block).comp
--   --   (tensor_product.assoc ℂ (ℍ_ x_2) (ℍ_ x_1) (ℍ_ x_1).symm.to_linear_map))
--   --   (x x_2 ⊗ₜ[ℂ] (m_ x_1 ⋆) (y x_1))
--   --   = 0 : _,
--   -- rw [linear_map.mul'_direct_sum_apply_include_block'],
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
  (linear_map.mul' ℂ ℍ) ∘ₗ (linear_map.mul' ℂ ℍ ⊗ₘ id)
    = linear_map.mul' ℂ ℍ ∘ₗ (id ⊗ₘ linear_map.mul' ℂ ℍ) ∘ₗ υ :=
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
