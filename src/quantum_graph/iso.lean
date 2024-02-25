/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.example

/-!
 # Isomorphisms between quantum graphs

 This file defines isomorphisms between quantum graphs.
-/

open tensor_product matrix
open_locale tensor_product big_operators kronecker functional

variables {p n : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]
local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(` x `)` := x →ₗ[ℂ] x

variables {φ : module.dual ℂ ℍ} [hφ : fact φ.is_faithful_pos_map]
  {ψ : module.dual ℂ (matrix p p ℂ)} (hψ : ψ.is_faithful_pos_map)

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y
local notation `m` := linear_map.mul' ℂ ℍ
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

private lemma commutes_with_mul''_adjoint [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : f φ.matrix = φ.matrix) :
  (tensor_product.map (f.to_alg_equiv.to_linear_map : ℍ →ₗ[ℂ] ℍ) (f.to_alg_equiv.to_linear_map : ℍ →ₗ[ℂ] ℍ))
    ∘ₗ ((m).adjoint : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ))
  = ((m).adjoint : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)) ∘ₗ f.to_alg_equiv.to_linear_map :=
begin
  simp_rw linear_map.comp_assoc,

  nth_rewrite_rhs 0 ← linear_map.adjoint_adjoint (((m).adjoint : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ∘ₗ f.to_alg_equiv.to_linear_map),
  have := (list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 0 1).mp hf,
  have this' : ∀ x y, f.symm.to_alg_equiv.to_linear_map (x * y)
    = f.symm.to_alg_equiv.to_linear_map x * f.symm.to_alg_equiv.to_linear_map y := λ x y,
  by simp_rw [alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv, _root_.map_mul],
  rw [linear_map.adjoint_comp, linear_map.adjoint_adjoint, this,
    ← (commutes_with_mul'_iff _).mpr this', linear_map.adjoint_comp, map_adjoint,
    ← this, linear_map.adjoint_adjoint],
end

open_locale matrix

lemma inner_aut_adjoint_eq_iff [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] (U : unitary_group n ℂ) :
  (inner_aut U).adjoint = inner_aut (star U) ↔ commute φ.matrix U :=
begin
  have hf : ∀ U : unitary_group n ℂ, inner_aut U = (inner_aut_star_alg U).to_alg_equiv.to_linear_map :=
  λ _, rfl,
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U),
  { intros V,
    ext1,
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star], },
  have hf' : inner_aut (star U) = (inner_aut_star_alg U).symm.to_alg_equiv.to_linear_map :=
  by rw [hh, hf],
  rw [hf, hf', (list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ (inner_aut_star_alg U)) 1 0),
    inner_aut_star_alg_apply, unitary_group.injective_mul U, matrix.mul_assoc,
    ← unitary_group.star_coe_eq_coe_star, unitary_group.star_mul_self, matrix.mul_one],
  exact ⟨λ h, h.symm, λ h, h.symm⟩,
end

lemma qam.mul'_adjoint_commutes_with_inner_aut_lm
  [hφ : fact φ.is_faithful_pos_map] [nontrivial n]
  {x : matrix.unitary_group n ℂ} (hx : commute φ.matrix x) :
  (tensor_product.map (inner_aut x) (inner_aut x)) ∘ₗ (m).adjoint = (m).adjoint ∘ₗ inner_aut x :=
begin
  simp_rw [commute, semiconj_by, mul_eq_mul] at hx,
  rw unitary_group.injective_mul x⁻¹ at hx,
  simp_rw [unitary_group.inv_apply, matrix.mul_assoc, unitary_group.mul_star_self,
    matrix.mul_one, ← matrix.mul_assoc, unitary_group.star_coe_eq_coe_star,
    ← inner_aut_apply', @eq_comm _ _ ((inner_aut x) _)] at hx,
  have hf : ∀ U : unitary_group n ℂ, inner_aut U = (inner_aut_star_alg U).to_alg_equiv.to_linear_map :=
  λ _, rfl,
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U),
  { intros V,
    ext1,
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star], },
  have hf' : inner_aut (star x) = (inner_aut_star_alg x).symm.to_alg_equiv.to_linear_map :=
  by rw [hh, hf],
  simp_rw [hf', hf] at *,
  rw [commutes_with_mul''_adjoint hx],
end

lemma qam.unit_commutes_with_inner_aut_lm (U : matrix.unitary_group n ℂ) :
  (inner_aut U) ∘ₗ η = η :=
begin
  rw [commutes_with_unit_iff, inner_aut_apply_one],
end

lemma qam.mul'_commutes_with_inner_aut_lm (x : matrix.unitary_group n ℂ) :
  m ∘ₗ ((tensor_product.map (inner_aut x) (inner_aut x)) : l(ℍ ⊗[ℂ] ℍ))
    = (inner_aut x) ∘ₗ (m : (ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] ℍ) :=
begin
  simp_rw [commutes_with_mul'_iff, mul_eq_mul, inner_aut.map_mul,
    eq_self_iff_true, forall_2_true_iff],
end

lemma qam.unit_adjoint_commutes_with_inner_aut_lm
  [hφ : fact φ.is_faithful_pos_map] [nontrivial n] {U : matrix.unitary_group n ℂ}
  (hU : commute φ.matrix U) :
  (η).adjoint ∘ₗ (inner_aut U) = (η).adjoint :=
begin
  rw [← inner_aut_adjoint_eq_iff] at hU,
  apply_fun linear_map.adjoint using linear_map.adjoint.injective,
  rw [linear_map.adjoint_comp, linear_map.adjoint_adjoint,
    hU, qam.unit_commutes_with_inner_aut_lm],
end

local notation `f_{`x`}` := inner_aut x

lemma inner_aut_is_real (U : unitary_group n ℂ) :
  (inner_aut U).is_real :=
λ x, (inner_aut.map_star _ _).symm

def star_alg_equiv.is_isometry [hφ : fact φ.is_faithful_pos_map] (f : ℍ ≃⋆ₐ[ℂ] ℍ) :
  Prop :=
∀ x, ‖f x‖ = ‖x‖

lemma inner_aut.to_matrix [hφ : fact φ.is_faithful_pos_map] (U : unitary_group n ℂ) :
  hφ.elim.to_matrix (inner_aut U)
    = U ⊗ₖ (hφ.elim.sig (-(1/2)) U)ᴴᵀ :=
begin
  ext1,
  simp only [module.dual.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv,
    module.dual.is_faithful_pos_map.inner_coord', module.dual.is_faithful_pos_map.basis_repr_apply,
    module.dual.is_faithful_pos_map.inner_coord'],
  simp only [inner_aut_star_alg_apply, mul_apply, std_basis_matrix, mul_ite, ite_mul, mul_zero,
    zero_mul, mul_one, one_mul, finset.sum_ite_irrel, finset.sum_ite_eq, finset.sum_ite_eq',
    finset.sum_const_zero, finset.mem_univ, if_true, ite_and, kronecker_map, of_apply,
    conj_apply, module.dual.is_faithful_pos_map.sig_apply, star_sum, star_mul',
    neg_neg, finset.mul_sum, finset.sum_mul, mul_assoc, inner_aut_apply',
    module.dual.is_faithful_pos_map.basis_apply],
  simp_rw [← star_apply, star_eq_conj_transpose, (pos_def.rpow.is_hermitian _ _).eq],
  rw finset.sum_comm,
  repeat { apply finset.sum_congr rfl, intros, },
  simp_rw [← star_eq_conj_transpose, ← unitary_group.star_coe_eq_coe_star],
  ring_nf,
end

lemma unitary_commutes_with_hφ_matrix_iff_is_isometry
  [hφ : fact φ.is_faithful_pos_map] [nontrivial n] (U : unitary_group n ℂ) :
  commute φ.matrix U ↔ @star_alg_equiv.is_isometry n _ _ φ _ (inner_aut_star_alg U) :=
begin
  rw [← inner_aut_adjoint_eq_iff, ← inner_aut_star_alg_equiv_to_linear_map,
    ← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map,
    (list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ (inner_aut_star_alg U)) 1 4),
    star_alg_equiv.is_isometry],
end

lemma qam.symm_apply_star_alg_equiv_conj [nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ _ f) (A : l(ℍ)) :
  qam.symm hφ.elim (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
    = f.to_alg_equiv.to_linear_map ∘ₗ (qam.symm hφ.elim A) ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
begin
  rw [star_alg_equiv.is_isometry, list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 4 1] at hf,
  simp only [qam.symm_eq_real_adjoint, linear_map.adjoint_comp,
    ← alg_equiv.to_linear_equiv_to_linear_map,
    linear_map.real_star_alg_equiv_conj],
  simp_rw [alg_equiv.to_linear_equiv_to_linear_map, hf],
  nth_rewrite 0 ←hf,
  simp only [linear_map.adjoint_adjoint, linear_map.comp_assoc],
end

lemma inner_aut.symmetric_eq [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] (A : l(ℍ)) {U : matrix.unitary_group n ℂ}
  (hU : commute φ.matrix U) :
  qam.symm hφ.elim (f_{U} ∘ₗ A ∘ₗ f_{star U}) = f_{U} ∘ₗ qam.symm hφ.elim A ∘ₗ f_{star U} :=
begin
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map,
      ← inner_aut_star_alg_equiv_to_linear_map],
  exact qam.symm_apply_star_alg_equiv_conj ((unitary_commutes_with_hφ_matrix_iff_is_isometry U).mp hU) _,
  -- simp_rw [← this, linear_map.adjoint_adjoint, linear_map.comp_assoc],
end

lemma star_alg_equiv.commutes_with_mul' (f : ℍ ≃⋆ₐ[ℂ] ℍ) :
  linear_map.mul' ℂ ℍ ∘ₗ (f.to_alg_equiv.to_linear_map ⊗ₘ f.to_alg_equiv.to_linear_map)
    = f.to_alg_equiv.to_linear_map ∘ₗ linear_map.mul' ℂ ℍ :=
begin
  rw [commutes_with_mul'_iff],
  intros x y,
  simp only [alg_equiv.to_linear_map_apply, _root_.map_mul],
end

lemma star_alg_equiv.is_isometry.commutes_with_mul'_adjoint [nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
  (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) :
  (f.to_alg_equiv.to_linear_map ⊗ₘ f.to_alg_equiv.to_linear_map)
    ∘ₗ (linear_map.mul' ℂ ℍ).adjoint
  = (linear_map.mul' ℂ ℍ).adjoint ∘ₗ f.to_alg_equiv.to_linear_map :=
begin
  rw [star_alg_equiv.is_isometry, list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 4 1] at hf,
  rw [← linear_map.adjoint_adjoint (f.to_alg_equiv.to_linear_map ⊗ₘ f.to_alg_equiv.to_linear_map),
    ← linear_map.adjoint_comp, tensor_product.map_adjoint, hf,
    f.symm.commutes_with_mul', linear_map.adjoint_comp, ← hf, linear_map.adjoint_adjoint],
end

lemma qam.refl_idempotent_star_alg_equiv_conj [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ _ f)
  (A B : l(ℍ)) :
  qam.refl_idempotent hφ.elim
    (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
    (f.to_alg_equiv.to_linear_map ∘ₗ B ∘ₗ f.symm.to_alg_equiv.to_linear_map)
  = f.to_alg_equiv.to_linear_map ∘ₗ (qam.refl_idempotent hφ.elim A B)
    ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
begin
  simp only [qam.refl_idempotent, linear_map.coe_mk, tensor_product.map_comp,
    ← linear_map.comp_assoc, f.commutes_with_mul'],
  have : f.symm.is_isometry,
  { simp_rw [star_alg_equiv.is_isometry] at hf ⊢,
    rw [list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f.symm) 4 1] at ⊢,
    rw [list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 4 1] at hf,
    rw [star_alg_equiv.symm_symm, ← hf, linear_map.adjoint_adjoint], },
  simp only [linear_map.comp_assoc, this.commutes_with_mul'_adjoint],
end

lemma inner_aut.refl_idempotent [nontrivial n] {U : unitary_group n ℂ} (hU : commute φ.matrix U)
  (A B : l(ℍ)) :
  qam.refl_idempotent hφ.elim (f_{U} ∘ₗ A ∘ₗ f_{star U}) (f_{U} ∘ₗ B ∘ₗ f_{star U})
    = f_{U} ∘ₗ qam.refl_idempotent hφ.elim A B ∘ₗ f_{star U} :=
begin
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map,
      ← inner_aut_star_alg_equiv_to_linear_map],
  exact qam.refl_idempotent_star_alg_equiv_conj ((unitary_commutes_with_hφ_matrix_iff_is_isometry U).mp hU) _ _,
end

lemma qam_star_alg_equiv_conj_iff [nontrivial n]
  {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) (A : l(ℍ)) :
  qam φ (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
    ↔ qam φ A :=
begin
  simp_rw [qam, qam.refl_idempotent_star_alg_equiv_conj hf,
    alg_equiv.comp_inj, alg_equiv.inj_comp],
end

lemma qam_symm_star_alg_equiv_conj_iff [nontrivial n]
  {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) (A : l(ℍ)) :
  @qam.is_symm n _ _ φ _ (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
  ↔ @qam.is_symm n _ _ φ _ A :=
begin
  simp only [qam.is_symm, qam.symm_apply_star_alg_equiv_conj hf,
    alg_equiv.comp_inj, alg_equiv.inj_comp],
end

lemma qam_is_self_adjoint_star_alg_equiv_conj_iff [nontrivial n]
  {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) (A : l(ℍ)) :
  _root_.is_self_adjoint (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
  ↔ _root_.is_self_adjoint A :=
begin
  simp only [linear_map.is_self_adjoint_iff', linear_map.adjoint_comp],
  rw [star_alg_equiv.is_isometry,
    list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 4 1] at hf,
  simp_rw [hf, ← linear_map.comp_assoc, alg_equiv.inj_comp, ← hf, linear_map.adjoint_adjoint,
    alg_equiv.comp_inj],
end

lemma qam_ir_reflexive_star_alg_equiv_conj [nontrivial n]
  {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) (A : l(ℍ)) :
  qam.refl_idempotent hφ.elim (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) 1
    = f.to_alg_equiv.to_linear_map ∘ₗ (qam.refl_idempotent hφ.elim A 1)
      ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
begin
  calc
    qam.refl_idempotent hφ.elim (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) 1
    =
    qam.refl_idempotent hφ.elim (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) (f.to_alg_equiv.to_linear_map ∘ₗ 1
      ∘ₗ f.symm.to_alg_equiv.to_linear_map) : _
  ... = f.to_alg_equiv.to_linear_map ∘ₗ (qam.refl_idempotent hφ.elim A 1)
      ∘ₗ f.symm.to_alg_equiv.to_linear_map : qam.refl_idempotent_star_alg_equiv_conj hf _ _,
  congr,
  simp only [linear_map.one_comp, ← star_alg_equiv.comp_eq_iff],
end

lemma qam_ir_reflexive'_star_alg_equiv_conj [nontrivial n]
  {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) (A : l(ℍ)) :
  qam.refl_idempotent hφ.elim 1 (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
    = f.to_alg_equiv.to_linear_map ∘ₗ (qam.refl_idempotent hφ.elim 1 A)
      ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
begin
  calc
    qam.refl_idempotent hφ.elim
      (1 : l(ℍ)) (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
    =
    qam.refl_idempotent hφ.elim (f.to_alg_equiv.to_linear_map ∘ₗ 1 ∘ₗ f.symm.to_alg_equiv.to_linear_map) (f.to_alg_equiv.to_linear_map ∘ₗ A
      ∘ₗ f.symm.to_alg_equiv.to_linear_map) : _
  ... = f.to_alg_equiv.to_linear_map ∘ₗ (qam.refl_idempotent hφ.elim 1 A)
      ∘ₗ f.symm.to_alg_equiv.to_linear_map : qam.refl_idempotent_star_alg_equiv_conj hf _ _,
  -- congr,
  simp only [linear_map.one_comp],
  have : 1 = f.to_alg_equiv.to_linear_map.comp f.symm.to_alg_equiv.to_linear_map :=
  by simp only [← star_alg_equiv.comp_eq_iff, linear_map.one_comp],
  simp only [← this],
end

lemma inner_aut.qam [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] {U : matrix.unitary_group n ℂ} (hU : commute φ.matrix U)
  (A : l(ℍ)) :
  qam φ (f_{U} ∘ₗ A ∘ₗ f_{star U}) ↔ qam φ A :=
begin
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map,
      ← inner_aut_star_alg_equiv_to_linear_map],
  exact qam_star_alg_equiv_conj_iff ((unitary_commutes_with_hφ_matrix_iff_is_isometry U).mp hU) _,
end

lemma inner_aut.ir_reflexive [nontrivial n] {U : matrix.unitary_group n ℂ} (hU : commute φ.matrix U)
  (A : l(ℍ)) :
  qam.refl_idempotent hφ.elim (f_{U} ∘ₗ A ∘ₗ f_{star U}) 1
    = f_{U} ∘ₗ (qam.refl_idempotent hφ.elim A 1) ∘ₗ f_{star U} :=
begin
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map,
      ← inner_aut_star_alg_equiv_to_linear_map],
  exact qam_ir_reflexive_star_alg_equiv_conj ((unitary_commutes_with_hφ_matrix_iff_is_isometry U).mp hU) _,
end

lemma inner_aut.qam_is_reflexive [nontrivial n] {U : matrix.unitary_group n ℂ}
  (hU : commute φ.matrix U) {A : l(ℍ)} :
  @qam_lm_nontracial_is_reflexive n _ _ φ _ (f_{U} ∘ₗ A ∘ₗ f_{star U})
  ↔ @qam_lm_nontracial_is_reflexive _ _ _ _ hφ A :=
begin
  simp_rw [qam_lm_nontracial_is_reflexive, inner_aut.ir_reflexive hU],
  nth_rewrite_lhs 0 linear_map.ext_iff,
  simp_rw [linear_map.comp_apply, inner_aut_eq_iff, linear_map.one_apply,
    ← linear_map.comp_apply, ← linear_map.ext_iff],
  rw ← linear_map.one_comp (inner_aut U⁻¹),
  simp_rw [inner_aut_inv_eq_star, ← inner_aut.inj_comp (star U)],
end

lemma inner_aut.qam_is_irreflexive [nontrivial n] {U : matrix.unitary_group n ℂ}
  (hU : commute φ.matrix U) {A : l(ℍ)} :
  @qam_lm_nontracial_is_unreflexive _ _ _ _ hφ (f_{U} ∘ₗ A ∘ₗ f_{star U})
  ↔ @qam_lm_nontracial_is_unreflexive _ _ _ _ hφ A :=
begin
  simp_rw [qam_lm_nontracial_is_unreflexive, inner_aut.ir_reflexive hU,
    linear_map.ext_iff, linear_map.comp_apply, inner_aut_eq_iff, linear_map.zero_apply,
    linear_map.map_zero],
  refine ⟨λ h x, _, λ h x, by rw h⟩,
  specialize h (f_{U} x),
  simp_rw [← inner_aut_inv_eq_star, inner_aut_inv_apply_inner_aut_self] at h,
  exact h,
end

def qam.iso (A B : l(ℍ)) :
  Prop :=
∃ f : ℍ ≃⋆ₐ[ℂ] ℍ, A ∘ₗ f.to_alg_equiv.to_linear_map = f.to_alg_equiv.to_linear_map ∘ₗ B
  ∧ f φ.matrix = φ.matrix

structure qam_iso [hφ : fact φ.is_faithful_pos_map] {A B : l(ℍ)} (hA : qam φ A) (hB : qam φ B)
  extends star_alg_equiv ℂ ℍ ℍ :=
(is_hom := A ∘ₗ to_star_alg_equiv.to_alg_equiv.to_linear_map = to_star_alg_equiv.to_alg_equiv.to_linear_map ∘ₗ B)
(is_iso := to_fun φ.matrix = φ.matrix)

-- -- TODO:
-- def qam.lm.reflexive.iso {A B : l(ℍ)} (hA : qam_lm_is_reflexive A)
--   (hB : qam_lm_is_reflexive B) :
--   Prop :=
-- ∃ f : ℍ ≃⋆ₐ[ℂ] ℍ, A ∘ f = f ∘ B

-- def qam.lm.unreflexive.iso {A B : l(ℍ)} (hA : qam_lm_is_unreflexive A)
--   (hB : qam_lm_is_unreflexive B) : Prop :=
-- ∃ f : ℍ ≃⋆ₐ[ℂ] ℍ, A ∘ f = f ∘ B

lemma qam.iso_iff [hφ : fact φ.is_faithful_pos_map]
  {A B : l(ℍ)} [nontrivial n] :
  @qam.iso n _ _ φ A B
    ↔ ∃ U : unitary_group n ℂ, A ∘ₗ inner_aut U = inner_aut U ∘ₗ B
      ∧ commute φ.matrix U :=
begin
  simp_rw [← inner_aut_adjoint_eq_iff],
  have hf : ∀ U : unitary_group n ℂ, f_{U} = (inner_aut_star_alg U).to_alg_equiv.to_linear_map :=
  λ _, rfl,
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U),
  { intros V,
    ext1,
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star], },
  have := λ U, list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _
    (inner_aut_star_alg U)) 1 0,
  simp_rw [hf, ← hh, this],
  split,
  { rintros ⟨f, hf⟩,
    obtain ⟨U, rfl⟩ := star_alg_equiv.of_matrix_is_inner f,
    exact ⟨U, hf⟩, },
  { rintros ⟨U, hU⟩,
    exact ⟨inner_aut_star_alg U, hU⟩, },
end

lemma qam.iso_preserves_spectrum (A B : l(ℍ))
  (h : @qam.iso n _ _ φ A B) :
  spectrum ℂ A = spectrum ℂ B :=
begin
  obtain ⟨f, ⟨hf, hh⟩⟩ := h,
  let f' := f.to_alg_equiv.to_linear_map,
  let f'' := f.symm.to_alg_equiv.to_linear_map,
  have hh' : f'' ∘ₗ f' = linear_map.id,
  { rw [linear_map.ext_iff],
    intros x,
    simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv, star_alg_equiv.symm_apply_apply, linear_map.id_apply], },
  have : B = f'' ∘ₗ A ∘ₗ f',
  { rw [hf, ← linear_map.comp_assoc, hh', linear_map.id_comp], },
  rw [this, ← spectrum.comm, linear_map.comp_assoc, linear_map.comp_eq_id_comm.mp hh',
    linear_map.comp_id],
end

-- MOVE:
lemma inner_aut_lm_rank_one [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] {U : matrix.unitary_group n ℂ}
  (hU : commute φ.matrix U) (x y : ℍ) :
  f_{U} ∘ₗ (|x⟩⟨y| : l(ℍ)) ∘ₗ f_{star U} = |f_{U} x⟩⟨f_{U} y| :=
begin
  rw ← inner_aut_adjoint_eq_iff at hU,
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, continuous_linear_map.coe_coe,
    rank_one_apply, smul_hom_class.map_smul, ← hU, linear_map.adjoint_inner_right,
    eq_self_iff_true, forall_true_iff],
end

local notation `e_{` x `,` y `}` := matrix.std_basis_matrix x y (1 : ℂ)

--MOVE:
lemma inner_aut_lm_basis_apply (U : matrix.unitary_group n ℂ) (i j k l : n) :
  (f_{U} e_{i,j}) k l = (U ⊗ₖ star U) (k,j) (i,l) :=
begin
  simp_rw [matrix.inner_aut_apply, matrix.mul_apply, matrix.unitary_group.inv_apply,
    matrix.std_basis_matrix, mul_boole, finset.sum_mul, ite_mul, zero_mul, ite_and,
    matrix.kronecker_map, matrix.of_apply],
  simp only [finset.sum_ite_eq, finset.mem_univ, if_true],
end

lemma qam.rank_one_to_matrix_of_star_alg_equiv_coord (x y : matrix n n ℂ) (i j k l : n) :
  hφ.elim.to_matrix (↑|x⟩⟨y|) (i,j) (k,l)
    = ((x ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2))
      ⊗ₖ (y ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2))ᴴᵀ) (i,k) (j,l) :=
begin
  simp_rw [rank_one_to_matrix, conj_transpose_col, mul_apply,
    col_apply, row_apply, pi.star_apply, reshape_apply, kronecker_apply, conj_apply],
  simp only [fintype.univ_punit, finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one, one_mul],
end
