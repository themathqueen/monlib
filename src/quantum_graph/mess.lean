/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.nontracial
import quantum_graph.to_projections
import quantum_graph.qam_A
import linear_algebra.my_bimodule
import quantum_graph.symm
import quantum_graph.schur_idempotent

/-!
 # Some messy stuff

 This file contains some messy stuff that I don't want to put in the main file.

 Will organise this later.
-/

variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]

open_locale tensor_product big_operators kronecker functional

local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

variables {φ : module.dual ℂ ℍ} [hφ : fact φ.is_faithful_pos_map]
  {ψ : module.dual ℂ (matrix p p ℂ)} (hψ : ψ.is_faithful_pos_map)

open_locale matrix
open matrix

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

noncomputable def ι_map (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, (id ⊗ₘ x) ((m).adjoint 1),
    map_add' := λ x y, by {
      obtain ⟨α, β, h⟩ := tensor_product.eq_span ((m).adjoint (1 : ℍ)),
      rw ← h,
      simp only [map_sum, tensor_product.map_tmul, linear_map.add_apply, tensor_product.tmul_add,
        finset.sum_add_distrib],
        },
    map_smul' := λ r x, by { simp_rw [ring_hom.id_apply, tensor_product.map_smul_right,
      linear_map.smul_apply], } },
end

lemma sig_neg_one (a : ℍ) :
  hφ.elim.sig (-1) a = φ.matrix ⬝ a ⬝ φ.matrix⁻¹ :=
begin
  simp_rw [module.dual.is_faithful_pos_map.sig_apply, neg_neg, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self],
end
lemma sig_one (a : ℍ) :
  hφ.elim.sig 1 a = φ.matrix⁻¹ ⬝ a ⬝ φ.matrix :=
begin
  simp_rw [module.dual.is_faithful_pos_map.sig_apply, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self],
end

lemma ι_map_apply_rank_one (a b : ℍ) :
  ι_map hφ.elim (|a⟩⟨b|) = hφ.elim.sig (-1) bᴴ ⊗ₜ[ℂ] a :=
begin
  simp_rw [ι_map, linear_map.coe_mk, linear_map.mul'_adjoint, one_apply, boole_mul,
    ite_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ, if_true, map_sum,
    smul_hom_class.map_smul, tensor_product.map_tmul, linear_map.one_apply,
    continuous_linear_map.coe_coe, rank_one_apply],
  have : ∀ i j, inner b (std_basis_matrix i j 1) = (φ.matrix ⬝ bᴴ) j i,
  { intros i j,
    rw [← inner_conj_symm, inner_std_basis_matrix_left, star_ring_end_apply,
      ← star_apply, star_eq_conj_transpose, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq], },
  simp_rw [this, ← tensor_product.smul_tmul, ← tensor_product.smul_tmul', smul_smul,
    mul_comm _ ((_ ⬝ _) _ _), ← finset.sum_smul, ← mul_apply, ← sig_neg_one,
    tensor_product.smul_tmul', ← smul_std_basis_matrix', ← tensor_product.sum_tmul],
  rw [← matrix_eq_sum_std_basis],
end

lemma ι_map_eq_Psi :
  ι_map hφ.elim = (id ⊗ₘ unop) ∘ₗ ten_swap ∘ₗ (hφ.elim.Psi 0 1).to_linear_map :=
begin
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [ι_map_apply_rank_one, linear_map.comp_apply, linear_equiv.coe_to_linear_map,
    module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    module.dual.is_faithful_pos_map.Psi_to_fun'_apply, ten_swap_apply, tensor_product.map_tmul,
    module.dual.is_faithful_pos_map.sig_conj_transpose, op_apply, unop_apply, mul_opposite.unop_op,
    module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply],
end
lemma ι_map_comp_inv :
  (ι_map hφ.elim) ∘ₗ ((hφ.elim.Psi 0 1).symm.to_linear_map ∘ₗ (ten_swap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ (id ⊗ₘ op))
    = 1 :=
begin
  rw linear_map.ext_iff,
  intros x,
  simp_rw [ι_map_eq_Psi, linear_map.comp_apply, linear_equiv.coe_to_linear_map,
    linear_equiv.apply_symm_apply, ten_swap_apply_ten_swap, ← linear_map.comp_apply,
    ← tensor_product.map_comp, unop_comp_op, linear_map.one_comp, tensor_product.map_one],
end
lemma ι_inv_comp_ι_map :
  ((hφ.elim.Psi 0 1).symm.to_linear_map ∘ₗ (ten_swap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ (id ⊗ₘ op)) ∘ₗ (ι_map hφ.elim)
    = 1 :=
begin
  rw [ι_map_eq_Psi],
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_to_linear_map,
    module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_mk, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_to_fun'_apply, ten_swap_apply,
    tensor_product.map_tmul, ten_swap_apply, module.dual.is_faithful_pos_map.Psi_inv_fun'_apply,
    neg_zero, module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply, op_unop,
    mul_opposite.unop_op, mul_opposite.op_unop, unop_op,
    conj_transpose_conj_transpose, module.dual.is_faithful_pos_map.sig_apply_sig,
    neg_add_self, module.dual.is_faithful_pos_map.sig_zero],
end
noncomputable def ι_inv_map (hφ : φ.is_faithful_pos_map) :
  (ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] l(ℍ) :=
((hφ.Psi 0 1).symm : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) ∘ₗ (ten_swap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ (id ⊗ₘ op)
noncomputable def ι_linear_equiv (hφ : φ.is_faithful_pos_map) :
  l(ℍ) ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
begin
  letI := fact.mk hφ,
  exact linear_equiv.of_linear (ι_map hφ) (ι_inv_map hφ) (ι_map_comp_inv) (ι_inv_comp_ι_map),
end

private noncomputable def phi_map_aux (hφ : fact φ.is_faithful_pos_map)
  (x : l(ℍ)) : l(ℍ ⊗[ℂ] ℍ) :=
(id ⊗ₘ m) ∘ₗ υ ∘ₗ (id ⊗ₘ x ⊗ₘ id) ∘ₗ ((m).adjoint ⊗ₘ id)
private lemma phi_map_aux_add (hφ : fact φ.is_faithful_pos_map)
  (x y : l(ℍ)) :
  phi_map_aux hφ (x + y) = phi_map_aux hφ x + phi_map_aux hφ y :=
begin
  simp_rw [phi_map_aux, tensor_product.map_add, tensor_product.add_map,
      linear_map.add_comp, linear_map.comp_add],
end
private lemma phi_map_aux_smul (hφ : fact φ.is_faithful_pos_map)
  (x : ℂ) (y : l(ℍ)) :
  phi_map_aux hφ (x • y) = x • phi_map_aux hφ y :=
begin
  apply tensor_product.ext',
  intros a b,
  rw [phi_map_aux, linear_map.comp_apply, tensor_product.map_smul, tensor_product.smul_map,
    linear_map.smul_apply, linear_map.smul_comp,
    linear_map.comp_smul, linear_map.smul_apply, smul_hom_class.map_smul],
  refl,
end

noncomputable def phi_map (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ) :=
{ to_fun := λ x, by letI := fact.mk hφ;
  exact (id ⊗ₘ m) ∘ₗ υ ∘ₗ (id ⊗ₘ x ⊗ₘ id) ∘ₗ ((m).adjoint ⊗ₘ id),
  map_add' := λ x y, phi_map_aux_add (fact.mk hφ) x y,
  map_smul' := λ x y, phi_map_aux_smul (fact.mk hφ) x y }

lemma module.dual.is_faithful_pos_map.sig_is_symmetric {t : ℝ} :
  linear_map.is_symmetric (hφ.elim.sig t).to_linear_map :=
begin
  rw [linear_map.is_symmetric_iff_is_self_adjoint, _root_.is_self_adjoint],
  exact module.dual.is_faithful_pos_map.sig_adjoint,
end

lemma ι_inv_map_mul_adjoint_eq_rmul :
  (ι_inv_map hφ.elim) ∘ₗ (m).adjoint = rmul :=
begin
  simp_rw [linear_map.ext_iff, ← matrix.ext_iff],
  intros x a i j,
  simp_rw [linear_map.comp_apply, linear_map.mul'_adjoint,
    map_sum, smul_hom_class.map_smul, ι_inv_map, linear_map.comp_apply,
    tensor_product.map_tmul, ten_swap_apply, module.dual.is_faithful_pos_map.Psi,
    linear_equiv.coe_coe, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_inv_fun'_apply, unop_apply, op_apply, mul_opposite.unop_op,
    neg_zero, module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply,
    std_basis_matrix_conj_transpose, star_one, linear_map.sum_apply, linear_map.smul_apply,
    matrix.sum_apply, pi.smul_apply, continuous_linear_map.coe_coe,
    rank_one_apply, pi.smul_apply, ← alg_equiv.to_linear_map_apply,
    module.dual.is_faithful_pos_map.sig_is_symmetric _ a, inner_std_basis_matrix_left,
    smul_eq_mul, std_basis_matrix, mul_boole, mul_ite, mul_zero, ite_and],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.sum_ite_eq',
    finset.mem_univ, if_true],
  simp_rw [mul_assoc, ← finset.mul_sum, ← mul_apply, mul_comm (x _ _), ← mul_apply,
    alg_equiv.to_linear_map_apply, ← matrix.mul_assoc, ← sig_one,
    ← module.dual.is_faithful_pos_map.sig_symm_eq, alg_equiv.apply_symm_apply],
  refl,
end

lemma Psi_inv_0_0_mul_adjoint_eq_lmul :
  ((hφ.elim.Psi 0 0).symm : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) →ₗ[ℂ] l(ℍ)) ∘ₗ (id ⊗ₘ op) ∘ₗ (m).adjoint = lmul :=
begin
  simp_rw [linear_map.ext_iff, ← matrix.ext_iff],
  intros x a i j,
  simp_rw [linear_map.comp_apply, linear_map.mul'_adjoint,
    map_sum, smul_hom_class.map_smul, tensor_product.map_tmul,
    module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_coe, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_inv_fun'_apply, unop_op, neg_zero,
    module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply,
    std_basis_matrix_conj_transpose, star_one, linear_map.sum_apply, linear_map.smul_apply,
    matrix.sum_apply, pi.smul_apply, continuous_linear_map.coe_coe,
    rank_one_apply, pi.smul_apply, inner_std_basis_matrix_left,
    smul_eq_mul, std_basis_matrix, mul_boole, mul_ite, mul_zero, ite_and],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.sum_ite_eq',
    finset.mem_univ, if_true],
  letI := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [mul_comm (x _ _), mul_assoc, ← finset.mul_sum, ← mul_apply, mul_comm _ ((_ ⬝ _) _ _),
    ← mul_apply, matrix.mul_assoc, mul_inv_of_invertible, matrix.mul_one],
  refl,
end

lemma ten_swap_Psi_eq_Psi_real {t s : ℝ} :
  ten_swap ∘ₗ (hφ.elim.Psi t s : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ)
    = (hφ.elim.Psi s t : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ).real :=
begin
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [linear_map.real_eq, linear_map.star_eq_adjoint, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint, rank_one_lm_eq_rank_one, linear_map.comp_apply, linear_equiv.coe_coe,
    module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    module.dual.is_faithful_pos_map.Psi_to_fun'_apply, ten_swap_apply,
    tensor_product.star_tmul, star, op_apply, mul_opposite.unop_op, conj_transpose_conj_transpose],
end

lemma rank_one_map_rank_one_eq [hφ : fact φ.is_faithful_pos_map] (x y z w : ℍ) :
  ((|x⟩⟨y| : l(ℍ)) ⊗ₘ (|z⟩⟨w| : l(ℍ))) = (|x ⊗ₜ[ℂ] z⟩⟨y ⊗ₜ[ℂ] w|) :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  simp_rw [tensor_product.map_tmul, continuous_linear_map.coe_coe, rank_one_apply,
    tensor_product.inner_tmul, tensor_product.smul_tmul_smul],
end

lemma phi_map_eq :
  phi_map hφ.elim = (rmul_map_lmul : (ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ)) ∘ₗ ι_map hφ.elim :=
begin
  apply linear_map.ext_of_rank_one',
  intros x y,
  rw tensor_product.ext_iff,
  intros a b,
  rw tensor_product.inner_ext_iff',
  intros c d,
  simp_rw [phi_map, linear_map.coe_mk, linear_map.comp_apply, tensor_product.map_tmul],
  obtain ⟨α, β, h⟩ := tensor_product.eq_span ((m).adjoint a),
  rw ← h,
  simp_rw [map_sum, tensor_product.sum_tmul, map_sum, linear_equiv.coe_coe,
    tensor_product.map_tmul, tensor_product.assoc_tmul, tensor_product.map_tmul,
    continuous_linear_map.coe_coe, linear_map.one_apply, rank_one_apply, linear_map.mul'_apply,
    sum_inner, smul_mul_assoc, tensor_product.tmul_smul, inner_smul_left, inner_conj_symm,
    tensor_product.inner_tmul, ← mul_assoc, mul_comm (inner (β _) _ : ℂ),
    ← finset.sum_mul, ← tensor_product.inner_tmul, ← sum_inner, h,
    linear_map.adjoint_inner_left, linear_map.mul'_apply, mul_eq_mul],
  rw [module.dual.is_faithful_pos_map.inner_left_conj _ _ y, ← tensor_product.inner_tmul],
  revert c d,
  rw [← tensor_product.inner_ext_iff', ι_map_apply_rank_one, rmul_map_lmul_apply],
  simp only [tensor_product.map_tmul, rmul_apply, lmul_apply, sig_neg_one, mul_eq_mul],
end

noncomputable def grad (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →+ (ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, ((x.adjoint ⊗ₘ id) - (id ⊗ₘ x)) ∘ₗ (m).adjoint,
    map_add' := λ x y, by { simp only [map_add, tensor_product.add_map,
      tensor_product.map_add, add_sub_add_comm, linear_map.add_comp], },
    map_zero' := by { simp only [map_zero, tensor_product.zero_map, tensor_product.map_zero,
      sub_zero, linear_map.zero_comp], } },
end

noncomputable def one_tensor_map :
  ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) :=
(id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
noncomputable def tensor_one_map :=
(η ⊗ₘ id) ∘ₗ τ⁻¹

lemma one_tensor_map_apply (x : ℍ) :
  one_tensor_map x = x ⊗ₜ 1 :=
by simp_rw [one_tensor_map, linear_map.comp_apply, linear_equiv.coe_coe,
  tensor_product.lid_symm_apply, tensor_product.comm_symm_tmul, tensor_product.map_tmul,
  linear_map.one_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul]
lemma tensor_one_map_apply (x : ℍ) :
  tensor_one_map x = 1 ⊗ₜ x :=
by simp_rw [tensor_one_map, linear_map.comp_apply, linear_equiv.coe_coe,
  tensor_product.lid_symm_apply, tensor_product.map_tmul,
  linear_map.one_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul]

private lemma grad_apply_rank_one (x y : ℍ) :
  grad hφ.elim (|x⟩⟨y|) =
    phi_map hφ.elim (|x⟩⟨y| : l(ℍ)).real ∘ₗ tensor_one_map
      - phi_map hφ.elim (|x⟩⟨y|) ∘ₗ one_tensor_map :=
begin
  rw linear_map.ext_iff,
  intros a,
  rw tensor_product.inner_ext_iff',
  intros c d,
  simp_rw [linear_map.sub_apply, inner_sub_left,
    linear_map.comp_apply, one_tensor_map_apply, tensor_one_map_apply, rank_one_real_apply, grad,
    add_monoid_hom.coe_mk, linear_map.sub_comp, linear_map.sub_apply, inner_sub_left,
    ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint, linear_map.comp_apply],
  obtain ⟨α, β, h⟩ := tensor_product.eq_span ((m).adjoint a),
  rw ← h,
  simp_rw [map_sum, sum_inner, tensor_product.map_tmul, rank_one_lm_eq_rank_one,
    phi_map_eq, linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    tensor_product.map_tmul, tensor_product.inner_tmul, continuous_linear_map.coe_coe,
    rank_one_apply, inner_smul_left, inner_conj_symm, linear_map.one_apply,
    mul_comm (inner (α _) _ : ℂ), mul_assoc, ← finset.mul_sum, ← tensor_product.inner_tmul,
    ← sum_inner, h, sum_inner, tensor_product.inner_tmul, mul_comm _ (inner (α _) _ : ℂ),
    ← mul_assoc, mul_comm _ (inner (α _) _ : ℂ), ← finset.sum_mul, ← tensor_product.inner_tmul,
    ← sum_inner, h, tensor_product.inner_tmul, linear_map.adjoint_inner_left,
    linear_map.mul'_apply, module.dual.is_faithful_pos_map.sig_conj_transpose,
    conj_transpose_conj_transpose, neg_neg, module.dual.is_faithful_pos_map.sig_apply_sig,
    neg_add_self, module.dual.is_faithful_pos_map.sig_zero, rmul_apply, lmul_apply, one_mul,
    mul_one, mul_eq_mul, ← module.dual.is_faithful_pos_map.inner_right_mul,
    sig_neg_one, ← module.dual.is_faithful_pos_map.inner_left_conj],
end
lemma grad_apply (x : l(ℍ)) :
  grad hφ.elim x =  phi_map hφ.elim x.real ∘ₗ tensor_one_map - phi_map hφ.elim x ∘ₗ one_tensor_map :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  rw [map_sum, linear_map.real_sum],
  simp_rw [map_sum, linear_map.sum_comp, ← finset.sum_sub_distrib, grad_apply_rank_one],
end

lemma one_tensor_map_adjoint [hφ : fact φ.is_faithful_pos_map] :
  (one_tensor_map : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)).adjoint = τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) :=
begin
  simp_rw [one_tensor_map, linear_map.adjoint_comp, ← linear_equiv.to_linear_map_eq_coe,
    tensor_product.lid_symm_adjoint, tensor_product.comm_symm_adjoint,
    tensor_product.map_adjoint, linear_map.adjoint_one, nontracial.unit_adjoint_eq,
    linear_equiv.to_linear_map_eq_coe, linear_map.comp_assoc],
end

lemma one_tensor_map_adjoint_apply [hφ : fact φ.is_faithful_pos_map] (x y : ℍ) :
  ((one_tensor_map : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)).adjoint) (x ⊗ₜ[ℂ] y) = φ y • x :=
by simp_rw [one_tensor_map_adjoint, linear_map.comp_apply, tensor_product.map_tmul,
  linear_equiv.coe_coe, tensor_product.comm_tmul, tensor_product.lid_tmul,
  linear_map.one_apply, nontracial.unit_adjoint_eq]

lemma tensor_one_map_adjoint [hφ : fact φ.is_faithful_pos_map] :
  (tensor_one_map : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)).adjoint = τ ∘ₗ ((η).adjoint ⊗ₘ id) :=
begin
  simp_rw [tensor_one_map, linear_map.adjoint_comp, ← linear_equiv.to_linear_map_eq_coe,
    tensor_product.lid_symm_adjoint, tensor_product.map_adjoint, linear_map.adjoint_one,
    nontracial.unit_adjoint_eq, linear_equiv.to_linear_map_eq_coe],
end

lemma tensor_one_map_adjoint_apply [hφ : fact φ.is_faithful_pos_map] (x y : ℍ) :
  ((tensor_one_map : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)).adjoint) (x ⊗ₜ y) = φ x • y :=
by simp_rw [tensor_one_map_adjoint, linear_map.comp_apply, tensor_product.map_tmul,
  linear_equiv.coe_coe, tensor_product.lid_tmul, linear_map.one_apply,
  nontracial.unit_adjoint_eq]

private lemma phi_map_adjoint_rank_one (x y : ℍ) :
  (phi_map hφ.elim (|x⟩⟨y|)).adjoint = phi_map hφ.elim (|x⟩⟨y| : l(ℍ)).real :=
begin
  simp_rw [phi_map_eq, rank_one_real_apply, linear_map.comp_apply,
    ι_map_apply_rank_one, rmul_map_lmul_apply, tensor_product.map_adjoint, rmul_eq_mul,
    lmul_eq_mul, linear_map.matrix.mul_left_adjoint, ← linear_map.matrix.mul_right_adjoint],
end
lemma phi_map_adjoint (x : l(ℍ)) :
  (phi_map hφ.elim x).adjoint = phi_map hφ.elim x.real :=
begin
  obtain ⟨α, β, h⟩ := x.exists_sum_rank_one,
  rw h,
  simp_rw [linear_map.real_sum, map_sum, phi_map_adjoint_rank_one],
end

private lemma grad_adjoint_rank_one (x y : ℍ) :
  (grad hφ.elim (|x⟩⟨y|)  : ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)).adjoint
    = τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim (|x⟩⟨y|)
    - τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim (|x⟩⟨y| : l(ℍ)).real :=
begin
  simp_rw [grad_apply_rank_one, map_sub, linear_map.adjoint_comp,
    tensor_one_map_adjoint, one_tensor_map_adjoint, ← phi_map_adjoint_rank_one,
    linear_map.adjoint_adjoint, linear_map.comp_assoc],
end
lemma grad_adjoint (x : l(ℍ)) :
  (grad hφ.elim x).adjoint = τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim x
    - τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim x.real :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  rw [linear_map.real_sum],
  simp only [map_sum, linear_map.sum_apply, linear_map.sum_comp, linear_map.comp_sum,
    grad_adjoint_rank_one, finset.sum_sub_distrib],
end

lemma sig_map_mul (t : ℝ) (x y : ℍ) :
  hφ.elim.sig t (x ⬝ y) = hφ.elim.sig t x ⬝ hφ.elim.sig t y :=
by simp only [← mul_eq_mul, _root_.map_mul]

private lemma phi_map_mul_rank_one (x y z w : ℍ) :
  phi_map hφ.elim (qam.refl_idempotent hφ.elim (|x⟩⟨y|) (|z⟩⟨w|))
    = phi_map hφ.elim (|x⟩⟨y|) ∘ₗ phi_map hφ.elim (|z⟩⟨w|) :=
begin
  simp_rw [qam.rank_one.refl_idempotent_eq, phi_map_eq, linear_map.comp_apply,
    ι_map_apply_rank_one, rmul_map_lmul_apply, ← tensor_product.map_comp, lmul_eq_mul,
    rmul_eq_mul, ← linear_map.mul_right_mul, ← linear_map.mul_left_mul,
    mul_eq_mul, ← sig_map_mul, ← conj_transpose_mul],
end
lemma phi_map_mul (A B : l(ℍ)) :
  phi_map hφ.elim (qam.refl_idempotent hφ.elim A B) = phi_map hφ.elim A ∘ₗ phi_map hφ.elim B :=
begin
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
  obtain ⟨γ, ζ, rfl⟩ := B.exists_sum_rank_one,
  -- rw [linear_map.eq_rank_one_of_faithful_pos_map hφ A,
  --   B.eq_rank_one_of_faithful_pos_map hφ],
  simp_rw [map_sum, linear_map.sum_apply, map_sum, phi_map_mul_rank_one,
    ← linear_map.sum_comp, ← linear_map.comp_sum],
end

lemma phi_map_of_real_Schur_idempotent {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  ((phi_map hφ.elim x).adjoint) = phi_map hφ.elim x ∧ is_idempotent_elem (phi_map hφ.elim x) :=
begin
  simp_rw [is_idempotent_elem, phi_map_adjoint, linear_map.mul_eq_comp, ← phi_map_mul,
    (linear_map.is_real_iff _).mp hx1, hx2, and_self],
end
@[instance] private def hmm {H : Type*} [normed_add_comm_group H]
  [inner_product_space ℂ H] [finite_dimensional ℂ H] (U : submodule ℂ H) :
  complete_space U :=
finite_dimensional.complete ℂ U
def phi_map_of_real_Schur_idempotent_orthogonal_projection {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  ∃ U : submodule ℂ (ℍ ⊗[ℂ] ℍ),
    (orthogonal_projection' U : l(ℍ ⊗[ℂ] ℍ)) = phi_map hφ.elim x :=
begin
  rw [orthogonal_projection_iff_lm, _root_.is_self_adjoint, linear_map.star_eq_adjoint],
  simp_rw [phi_map_of_real_Schur_idempotent hx1 hx2, and_true],
end
noncomputable def phi_map_of_real_Schur_idempotent.submodule {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  submodule ℂ (ℍ ⊗[ℂ] ℍ) :=
by choose U hU using phi_map_of_real_Schur_idempotent_orthogonal_projection hx1 hx2; exact U
def phi_map_of_real_Schur_idempotent.orthogonal_projection_eq {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  (orthogonal_projection' (phi_map_of_real_Schur_idempotent.submodule hx1 hx2) : l(ℍ ⊗[ℂ] ℍ))
    = phi_map hφ.elim x :=
phi_map_of_real_Schur_idempotent.submodule._proof_11 hx1 hx2

lemma grad_apply_of_real_Schur_idempotent {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  (phi_map hφ.elim x) ∘ₗ (grad hφ.elim x) = grad hφ.elim x :=
begin
  simp_rw [grad_apply, (linear_map.is_real_iff _).mp hx1, ← linear_map.comp_sub,
    ← linear_map.comp_assoc, ← phi_map_mul, hx2],
end

lemma grad_of_real_Schur_idempotent_range {x : l(ℍ)} (hx1 : x.is_real)
  (hx2 : qam.refl_idempotent hφ.elim x x = x) :
  (grad hφ.elim x).range ≤ phi_map_of_real_Schur_idempotent.submodule hx1 hx2 :=
begin
  rw [← grad_apply_of_real_Schur_idempotent hx1 hx2,
    ← phi_map_of_real_Schur_idempotent.orthogonal_projection_eq hx1 hx2],
  nth_rewrite 0 ← orthogonal_projection.range
    (phi_map_of_real_Schur_idempotent.submodule hx1 hx2),
  rw [linear_map.range_le_iff_comap],
  -- rw [range_le_iff_comap],
  apply submodule.ext,
  simp_rw [submodule.mem_top, iff_true, submodule.mem_comap, linear_map.comp_apply,
    continuous_linear_map.coe_coe],
  intros a,
  exact linear_map.mem_range_self _ _,
end

noncomputable def D_in :
  l(ℍ) →ₗ[ℂ] l(ℍ) :=
{ to_fun := λ x, m ∘ₗ (x ⊗ₘ id) ∘ₗ tensor_one_map,
  map_add' := λ x y, by { simp only [tensor_product.add_map,
    linear_map.comp_add, linear_map.add_comp], },
  map_smul' := λ r x, by { simp only [tensor_product.smul_map,
    linear_map.comp_smul, linear_map.smul_comp, ring_hom.id_apply], } }
noncomputable def D_out (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →+ l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, m ∘ₗ (id ⊗ₘ x.adjoint) ∘ₗ one_tensor_map,
    map_add' := λ x y, by { simp only [map_add, tensor_product.map_add,
      linear_map.comp_add, linear_map.add_comp], },
    map_zero' := by { simp only [map_zero, tensor_product.map_zero, linear_map.zero_comp,
      linear_map.comp_zero], } },
end

lemma D_in_apply (x : l(ℍ)) :
  D_in x = lmul (x 1) :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [D_in, linear_map.coe_mk, linear_map.comp_apply, tensor_one_map_apply,
    tensor_product.map_tmul, linear_map.mul'_apply, linear_map.one_apply, lmul_apply],
end
lemma D_out_apply (x : l(ℍ)) :
  D_out hφ.elim x = rmul (x.adjoint 1) :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [D_out, add_monoid_hom.coe_mk, linear_map.comp_apply, one_tensor_map_apply,
    tensor_product.map_tmul, linear_map.mul'_apply, linear_map.one_apply, rmul_apply],
end

lemma tensor_one_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one (x y : ℍ) :
  τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim (|x⟩⟨y|) ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
  = |x⟩⟨y| :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.lid_symm_apply,
    tensor_product.comm_symm_tmul, tensor_product.map_tmul, linear_map.one_apply,
    algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, phi_map_eq, linear_map.comp_apply, ι_map_apply_rank_one,
    rmul_map_lmul_apply, tensor_product.map_tmul, tensor_product.lid_tmul,
    lmul_apply, rmul_apply, nontracial.unit_adjoint_eq],
  have := module.dual.is_faithful_pos_map.mul_left hφ.elim aᴴ y 1,
  rw [matrix.one_mul, matrix.mul_one, ← sig_neg_one, conj_transpose_conj_transpose,
    conj_transpose_mul, conj_transpose_conj_transpose] at this,
  simp only [linear_map.one_apply, mul_one, mul_one, mul_eq_mul, ← this, one_smul,
    matrix.mul_one],
  rw [continuous_linear_map.coe_coe, rank_one_apply, module.dual.is_faithful_pos_map.inner_eq],
end
lemma tensor_one_map_adjoint_comp_phi_map_comp_one_tensor_map (x : l(ℍ)) :
  τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = x :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    linear_map.sum_apply, tensor_one_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one],
end

lemma linear_functional_comp_sig (t : ℝ) :
  φ ∘ₗ (hφ.elim.sig t).to_linear_map = φ :=
begin
  ext1 x,
  simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, φ.apply],
  nth_rewrite 0 [← sig_apply_pos_def_matrix' t],
  simp_rw [← mul_eq_mul],
  rw [← _root_.map_mul, aut_mat_inner_trace_preserving],
end

private lemma tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one (x y : ℍ) :
  τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim (|x⟩⟨y|) ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹
  = D_in (|x⟩⟨y| : l(ℍ)) :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.lid_symm_apply,
    tensor_product.map_tmul, linear_map.one_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, phi_map_eq,
    linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    tensor_product.map_tmul, tensor_product.lid_tmul, lmul_apply, rmul_apply, nontracial.unit_adjoint_eq,
    one_smul, one_mul, linear_map.one_apply, D_in_apply, lmul_eq_mul,
    continuous_linear_map.coe_coe, rank_one_apply, linear_map.mul_left_apply,
    ← alg_equiv.to_linear_map_apply, ← linear_map.comp_apply, linear_functional_comp_sig,
    module.dual.is_faithful_pos_map.inner_eq, matrix.mul_one, smul_mul_assoc],
end
lemma tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map (x : l(ℍ)) :
  τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ phi_map hφ.elim x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = D_in x :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    linear_map.sum_apply, tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one],
end

private lemma one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one (x y : ℍ) :
  τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim (|x⟩⟨y|) ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹
  = (((|x⟩⟨y| : l(ℍ)).real).adjoint) :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.lid_symm_apply,
    tensor_product.map_tmul, linear_map.one_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, phi_map_eq,
    linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    tensor_product.map_tmul, tensor_product.comm_tmul, tensor_product.lid_tmul,
    lmul_apply, rmul_apply, nontracial.unit_adjoint_eq, one_smul, one_mul, linear_map.one_apply,
    rank_one_real_apply, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint,
    rank_one_lm_apply, module.dual.is_faithful_pos_map.inner_eq, conj_transpose_conj_transpose, mul_eq_mul],
end

lemma one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map (x : l(ℍ)) :
  τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = ((x.real).adjoint) :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    linear_map.sum_apply, one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one,
    linear_map.real_sum],
end

private lemma one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one (x y : ℍ) :
  τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim (|x⟩⟨y|) ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
  = D_out hφ.elim (|x⟩⟨y| : l(ℍ)).real :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.lid_symm_apply,
    tensor_product.comm_symm_tmul, tensor_product.map_tmul, linear_map.one_apply,
    algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, phi_map_eq, linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    tensor_product.map_tmul, tensor_product.comm_tmul, tensor_product.lid_tmul,
    lmul_apply, rmul_apply, nontracial.unit_adjoint_eq, one_smul, mul_one, linear_map.one_apply,
    D_out_apply, rmul_eq_mul, rank_one_real_apply, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint, linear_map.mul_right_apply, rank_one_lm_apply,
    ← alg_equiv.to_linear_map_apply, module.dual.is_faithful_pos_map.inner_eq, matrix.mul_one, conj_transpose_conj_transpose,
    mul_smul_comm],
end
lemma one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map (x : l(ℍ)) :
  τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ (η).adjoint) ∘ₗ phi_map hφ.elim x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = D_out hφ.elim x.real :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp only [D_out_apply, map_sum, linear_map.real_sum, map_sum],
  simp_rw [← D_out_apply],
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    linear_map.sum_apply,
    one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one,
    linear_map.real_sum],
end

private lemma qam.refl_idempotent_real_rank_one (a b c d : ℍ) :
  (qam.refl_idempotent hφ.elim (|a⟩⟨b|) (|c⟩⟨d|)).real = qam.refl_idempotent hφ.elim (|c⟩⟨d| : l(ℍ)).real (|a⟩⟨b| : l(ℍ)).real :=
begin
  simp only [qam.rank_one.refl_idempotent_eq, rank_one_real_apply,
    ← sig_map_mul, ← conj_transpose_mul],
end

lemma qam.refl_idempotent_real (a b : l(ℍ)) :
  (qam.refl_idempotent hφ.elim a b).real = qam.refl_idempotent hφ.elim b.real a.real :=
begin
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one,
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rank_one,
  simp only [map_sum, linear_map.real_sum, linear_map.sum_apply,
    qam.refl_idempotent_real_rank_one],
  rw finset.sum_comm,
end
lemma qam.refl_idempotent_adjoint (a b : l(ℍ)) :
  (qam.refl_idempotent hφ.elim a b).adjoint = qam.refl_idempotent hφ.elim (a.adjoint) (b.adjoint) :=
begin
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one,
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rank_one,
  simp_rw [map_sum, linear_map.sum_apply, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint, rank_one_lm_eq_rank_one, qam.rank_one.refl_idempotent_eq,
    map_sum, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint],
end

private lemma D_in_Schur_product_eq_ir_refl_rank_one (a b c d : ℍ) :
  D_in (qam.refl_idempotent hφ.elim (|a⟩⟨b|) (|c⟩⟨d|))
    = qam.refl_idempotent hφ.elim ((|a⟩⟨b| : l(ℍ)) ∘ₗ ((|c⟩⟨d| : l(ℍ)).real.adjoint)) id :=
begin
  simp_rw [D_in_apply, rank_one_real_apply, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint,
    rank_one_lm_comp_rank_one_lm, smul_hom_class.map_smul,
    linear_map.smul_apply, rank_one_lm_eq_rank_one],
  rw [qam.rank_one.refl_idempotent_eq, qam.reflexive_eq_rank_one,
    continuous_linear_map.coe_coe, rank_one_apply, module.dual.is_faithful_pos_map.inner_right_conj,
    sig_neg_one, conj_transpose_conj_transpose, matrix.one_mul,
    smul_hom_class.map_smul, lmul_eq_mul],
end

lemma D_in_Schur_product_eq_ir_refl (A B : l(ℍ)) :
  D_in (qam.refl_idempotent hφ.elim A B) = qam.refl_idempotent hφ.elim (A ∘ₗ (B.real.adjoint)) id :=
begin
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_apply, linear_map.real_sum, linear_map.comp_sum,
    linear_map.sum_comp, D_in_Schur_product_eq_ir_refl_rank_one],
end

private lemma D_out_Schur_product_eq_ir_refl'_rank_one (a b c d : ℍ) :
  D_out hφ.elim (qam.refl_idempotent hφ.elim (|a⟩⟨b|) (|c⟩⟨d|))
    = qam.refl_idempotent hφ.elim id ((|c⟩⟨d| : l(ℍ)).adjoint ∘ₗ (|a⟩⟨b| : l(ℍ)).real) :=
begin
  simp_rw [D_out_apply, rank_one_real_apply, qam.rank_one.refl_idempotent_eq,
    ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint, rank_one_lm_comp_rank_one_lm,
    smul_hom_class.map_smul, rank_one_lm_eq_rank_one, qam.reflexive'_eq_rank_one,
    continuous_linear_map.coe_coe, rank_one_apply, smul_hom_class.map_smul,
    module.dual.is_faithful_pos_map.sig_conj_transpose, conj_transpose_conj_transpose,
    module.dual.is_faithful_pos_map.sig_apply_sig, add_neg_self,
    module.dual.is_faithful_pos_map.sig_zero, module.dual.is_faithful_pos_map.inner_left_mul,
    matrix.mul_one],
  refl,
end

lemma D_out_Schur_product_eq_ir_refl' (A B : l(ℍ)) :
  D_out hφ.elim (qam.refl_idempotent hφ.elim A B)
    = qam.refl_idempotent hφ.elim id (B.adjoint ∘ₗ A.real) :=
begin
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_apply, linear_map.real_sum, linear_map.comp_sum,
    linear_map.sum_comp, D_out_Schur_product_eq_ir_refl'_rank_one],
  rw finset.sum_comm,
end

lemma grad_adjoint_grad (x : l(ℍ)) :
  (grad hφ.elim x).adjoint ∘ₗ grad hφ.elim x
  = D_in (qam.refl_idempotent hφ.elim x x.real)
    - qam.refl_idempotent hφ.elim x x
    - qam.refl_idempotent hφ.elim (x.adjoint) (x.adjoint)
    + D_out hφ.elim (qam.refl_idempotent hφ.elim x.real x) :=
begin
  simp_rw [grad, add_monoid_hom.coe_mk, linear_map.adjoint_comp, map_sub,
    linear_map.adjoint_adjoint, tensor_product.map_adjoint, linear_map.adjoint_one,
    linear_map.adjoint_adjoint],
  simp only [linear_map.comp_sub, linear_map.sub_comp],
  simp_rw [← linear_map.comp_assoc, linear_map.comp_assoc (_ ⊗ₘ _) (_ ⊗ₘ _),
    ← tensor_product.map_comp, linear_map.one_comp, linear_map.comp_one,
    D_in_Schur_product_eq_ir_refl, D_out_Schur_product_eq_ir_refl', qam.refl_idempotent,
    schur_idempotent,
    linear_map.coe_mk, linear_map.real_real, linear_map.comp_assoc,
    sub_eq_add_neg, neg_add, neg_neg, add_assoc],
end

lemma ι_inv_grad_apply_rank_one (a b x : ℍ) :
  (ι_inv_map hφ.elim) ((grad hφ.elim (|a⟩⟨b|)) x) = rmul x ∘ₗ (|a⟩⟨b| : l(ℍ)).real - (|a⟩⟨b| : l(ℍ)) ∘ₗ rmul x :=
begin
  simp_rw [grad_apply, ι_inv_map, linear_map.comp_apply, linear_map.sub_apply, map_sub,
    linear_map.comp_apply, tensor_one_map_apply, one_tensor_map_apply,
    phi_map_eq, linear_map.comp_apply, rank_one_real_apply, ι_map_apply_rank_one,
    rmul_map_lmul_apply, tensor_product.map_tmul, ten_swap_apply,
    linear_equiv.coe_coe, module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_inv_fun'_apply, neg_zero,
    module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply, op_apply, unop_apply,
    mul_opposite.unop_op, module.dual.is_faithful_pos_map.sig_conj_transpose,
    module.dual.is_faithful_pos_map.sig_apply_sig, neg_neg, neg_add_self,
    module.dual.is_faithful_pos_map.sig_zero, lmul_apply, rmul_apply],
  rw [← @linear_map.mul_right_apply ℂ _ _ _ _ _ _ x aᴴ, ← linear_map.comp_rank_one],
  simp_rw [conj_transpose_one, mul_one, one_mul, mul_eq_mul, conj_transpose_mul, sig_map_mul,
    module.dual.is_faithful_pos_map.sig_conj_transpose,
    module.dual.is_faithful_pos_map.sig_apply_sig,
    add_neg_self, module.dual.is_faithful_pos_map.sig_zero, ← mul_eq_mul,
    conj_transpose_conj_transpose, ← @linear_map.mul_right_apply ℂ _ _ _ _ _ _ _ b,
    ← linear_map.matrix.mul_right_adjoint, ← linear_map.rank_one_comp],
  refl,
end

lemma ι_inv_map_apply (x y : ℍ) :
  ι_inv_map hφ.elim (x ⊗ₜ[ℂ] y) = |y⟩⟨hφ.elim.sig (-1) xᴴ| :=
begin
  simp_rw [ι_inv_map, linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.map_tmul,
    ten_swap_apply, module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_inv_fun'_apply, op_apply, unop_apply, mul_opposite.unop_op,
    neg_zero, module.dual.is_faithful_pos_map.sig_zero, linear_map.one_apply],
end

lemma phi_map_eq' (x : l(ℍ)) :
  phi_map hφ.elim x = ι_map hφ.elim ∘ₗ (qam.refl_idempotent hφ.elim x) ∘ₗ ι_inv_map hφ.elim :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp_rw [map_sum, linear_map.sum_comp, linear_map.comp_sum],
  apply finset.sum_congr rfl, intros,
  rw [tensor_product.ext_iff],
  intros a b,
  simp_rw [phi_map_eq, linear_map.comp_apply, ι_inv_map_apply, ι_map_apply_rank_one,
    rmul_map_lmul_apply, tensor_product.map_tmul, qam.rank_one.refl_idempotent_eq,
    ι_map_apply_rank_one, rmul_apply, lmul_apply, conj_transpose_mul,
    module.dual.is_faithful_pos_map.sig_conj_transpose, sig_map_mul,
    module.dual.is_faithful_pos_map.sig_apply_sig, add_neg_self,
    module.dual.is_faithful_pos_map.sig_zero, conj_transpose_conj_transpose],
  refl,
end

lemma phi_map_maps_to_bimodule_maps {A : l(ℍ)} :
  (phi_map hφ.elim A).is_bimodule_map :=
begin
  intros x y a,
  obtain ⟨α, β, rfl⟩ := tensor_product.eq_span a,
  obtain ⟨γ, ζ, rfl⟩ := A.exists_sum_rank_one,
  simp_rw [map_sum, linear_map.sum_apply, bimodule.lsmul_sum, bimodule.sum_rsmul,
    phi_map_eq, linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    map_sum],
  simp only [bimodule.rsmul_apply, bimodule.lsmul_apply, tensor_product.map_tmul,
    rmul_apply, lmul_apply, matrix.mul_assoc],
  rw finset.sum_comm,
  simp only [mul_assoc],
end
lemma phi_map_range :
  (phi_map hφ.elim).range ≤ is_bimodule_map.submodule :=
begin
  intros A,
  simp_rw [linear_map.mem_range],
  rintros ⟨y, rfl⟩,
  exact phi_map_maps_to_bimodule_maps,
end

lemma orthonormal_basis_tensor_product_sum_repr (a b : ℍ) :
  ∑ (x_3 x_4 : n × n),
    ⟪((hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)), a ⊗ₜ[ℂ] b⟫_ℂ
      • (hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4) = a ⊗ₜ b :=
begin
  simp_rw [basis.tensor_product_apply', tensor_product.inner_tmul,
    ← tensor_product.smul_tmul_smul, ← tensor_product.tmul_sum,
    ← tensor_product.sum_tmul, module.dual.is_faithful_pos_map.basis_apply,
    ← module.dual.is_faithful_pos_map.orthonormal_basis_apply,
    ← orthonormal_basis.repr_apply_apply, orthonormal_basis.sum_repr],
end

lemma linear_map.tensor_matrix_eq_rank_one (x : l(ℍ ⊗[ℂ] ℍ)) :
  x = ∑ i j k l, ⟪(basis.tensor_product hφ.elim.basis hφ.elim.basis) (i,j), x ((basis.tensor_product hφ.elim.basis hφ.elim.basis) (k,l))⟫_ℂ •
    |(basis.tensor_product hφ.elim.basis hφ.elim.basis) (i,j)⟩⟨(basis.tensor_product hφ.elim.basis hφ.elim.basis) (k,l)| :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  rw tensor_product.inner_ext_iff',
  intros c d,
  simp_rw [linear_map.sum_apply, linear_map.smul_apply, sum_inner, inner_smul_left,
    continuous_linear_map.coe_coe, rank_one_apply, inner_smul_left, inner_conj_symm],
  have := calc ∑ (x_1 x_2 x_3 x_4 : n × n),
    ⟪x ((hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)),
        (hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2)⟫_ℂ
      * ⟪(a ⊗ₜ[ℂ] b), (hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)⟫_ℂ
      * ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ
    = ⟪x (∑ x_3 x_4 : n × n, ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4), (a ⊗ₜ[ℂ] b)⟫_ℂ
      • (hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)),
    ∑ x_1 x_2 : n × n, ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ
      • (hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2)⟫_ℂ : _
  ... = ⟪x (a ⊗ₜ b), c ⊗ₜ d⟫_ℂ : _,
  { simp_rw [← this, mul_assoc], },
  { simp_rw [map_sum, inner_sum, sum_inner, smul_hom_class.map_smul, inner_smul_left,
      inner_smul_right, inner_conj_symm],
    repeat { apply finset.sum_congr rfl, intros, },
    simp only [← mul_assoc, mul_comm, mul_rotate],
    rw mul_comm ⟪a ⊗ₜ b, _⟫_ℂ ⟪_, c ⊗ₜ d⟫_ℂ, },
  { simp_rw [orthonormal_basis_tensor_product_sum_repr], },
end

noncomputable def phi_inv_map (hφ : φ.is_faithful_pos_map) :
  (is_bimodule_map.submodule : submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ) :=
{ to_fun := λ x, ι_inv_map hφ ((x : l(ℍ ⊗[ℂ] ℍ)) 1),
  map_add' := λ x y, by { simp_rw [submodule.coe_add, linear_map.add_apply, map_add], },
  map_smul' := λ r x, by { simp only [submodule.coe_smul,
    linear_map.smul_apply, smul_hom_class.map_smul, ring_hom.id_apply], } }

noncomputable def phi_inv'_map (hφ : φ.is_faithful_pos_map) :
  l(ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, τ ∘ₗ ((η).adjoint ⊗ₘ id) ∘ₗ (x : l(ℍ ⊗[ℂ] ℍ)) ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹,
    map_add' := λ x y, by { simp only [submodule.coe_add, linear_map.add_comp,
      linear_map.comp_add], },
    map_smul' := λ r x, by { simp only [submodule.coe_smul, linear_map.comp_smul,
      linear_map.smul_comp, smul_hom_class.map_smul, ring_hom.id_apply], } },
end
noncomputable def phi_inv'_map_coe (hφ : φ.is_faithful_pos_map) :
  (is_bimodule_map.submodule : submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, phi_inv'_map hφ x,
    map_add' := λ x y, by { simp only [phi_inv'_map, linear_map.coe_mk, submodule.coe_add,
      linear_map.add_comp, linear_map.comp_add], },
    map_smul' := λ r x, by { simp only [phi_inv'_map, linear_map.coe_mk, submodule.coe_smul,
      linear_map.comp_smul, linear_map.smul_comp, smul_hom_class.map_smul, ring_hom.id_apply], } },
end

lemma phi_inv'_map_apply (x y : l(ℍ)) :
  phi_inv'_map hφ.elim (x ⊗ₘ y) = y ∘ₗ (|(1 : ℍ)⟩⟨(1 : ℍ)| : l(ℍ)) ∘ₗ x :=
begin
  simp_rw [linear_map.ext_iff],
  intros a,
  simp_rw [phi_inv'_map, linear_map.coe_mk, linear_map.comp_apply, linear_equiv.coe_coe,
    tensor_product.lid_symm_apply, tensor_product.comm_symm_tmul, tensor_product.map_tmul,
    tensor_product.lid_tmul, continuous_linear_map.coe_coe, linear_map.one_apply,
    algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, nontracial.unit_adjoint_eq, rank_one_apply, module.dual.is_faithful_pos_map.inner_eq,
    conj_transpose_one, one_smul, matrix.one_mul, smul_hom_class.map_smul],
end

lemma ι_linear_equiv_apply_eq (x : l(ℍ)) :
  ι_linear_equiv hφ.elim x = ι_map hφ.elim x :=
rfl
lemma ι_linear_equiv_symm_apply_eq (x : ℍ ⊗[ℂ] ℍ) :
  (ι_linear_equiv hφ.elim).symm x = ι_inv_map hφ.elim x :=
rfl

private noncomputable def phi_map_coe_aux (hφ : fact φ.is_faithful_pos_map)
  (x : l(ℍ)) :
  (is_bimodule_map.submodule : submodule ℂ l(ℍ ⊗[ℂ] ℍ)) :=
⟨phi_map hφ.elim x, phi_map_maps_to_bimodule_maps⟩

private lemma phi_map_coe_aux_add (hφ : fact φ.is_faithful_pos_map) (x y : l(ℍ)) :
  phi_map_coe_aux hφ (x + y) = phi_map_coe_aux hφ x + phi_map_coe_aux hφ y :=
begin
  simp only [phi_map_coe_aux, map_add],
  ext1,
  simp only [linear_map.add_apply, submodule.coe_add, subtype.coe_mk],
end
private lemma phi_map_coe_aux_smul (hφ : fact φ.is_faithful_pos_map) (r : ℂ) (x : l(ℍ)) :
  phi_map_coe_aux hφ (r • x) = r • phi_map_coe_aux hφ x :=
begin
  simp only [phi_map_coe_aux, smul_hom_class.map_smul],
  ext1,
  simp only [linear_map.smul_apply, submodule.coe_smul, subtype.coe_mk],
end

noncomputable def phi_map_coe (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →ₗ[ℂ] (is_bimodule_map.submodule : submodule ℂ l(ℍ ⊗[ℂ] ℍ)) :=
{ to_fun := λ x, by letI := fact.mk hφ; exact ⟨phi_map hφ x, phi_map_maps_to_bimodule_maps⟩,
  map_add' := phi_map_coe_aux_add (fact.mk hφ),
  map_smul' := phi_map_coe_aux_smul (fact.mk hφ) }

lemma phi_map_left_inverse :
  phi_inv_map hφ.elim ∘ₗ phi_map_coe hφ.elim = 1 :=
begin
  apply linear_map.ext_of_rank_one',
  intros x y,
  simp_rw [linear_map.one_apply, linear_map.comp_apply, phi_map_coe,
    linear_map.coe_mk, phi_map_eq', phi_inv_map, linear_map.coe_mk, subtype.coe_mk],
  simp_rw [linear_map.comp_apply],
  simp_rw [← ι_linear_equiv_apply_eq, ← ι_linear_equiv_symm_apply_eq,
    linear_equiv.symm_apply_apply],
  have : (ι_linear_equiv hφ.elim).symm 1 = qam.complete_graph ℍ,
  { simp_rw [ι_linear_equiv_symm_apply_eq, algebra.tensor_product.one_def,
      ι_inv_map_apply, conj_transpose_one, _root_.map_one],
    refl, },
  rw [this, qam.refl_idempotent, qam.refl_idempotent_complete_graph_right],
end

lemma phi_inv'_map_phi_map :
  phi_inv'_map_coe hφ.elim ∘ₗ phi_map_coe hφ.elim = 1 :=
begin
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [phi_inv'_map_coe, phi_map_coe, linear_map.comp_apply, linear_map.coe_mk,
    phi_map_eq, linear_map.comp_apply, ι_map_apply_rank_one, rmul_map_lmul_apply,
    subtype.coe_mk, phi_inv'_map_apply, rmul_eq_mul,
    ← linear_map.matrix.mul_right_adjoint, linear_map.rank_one_comp',
    linear_map.comp_rank_one, lmul_apply, linear_map.mul_right_apply,
    mul_one, one_mul, linear_map.one_apply],
end

lemma phi_map_right_inverse (x : {x : l(ℍ ⊗[ℂ] ℍ) // x.is_bimodule_map}) :
  phi_map_coe hφ.elim (phi_inv_map hφ.elim x) = x :=
begin
  simp_rw [phi_inv_map, linear_map.coe_mk, phi_map_coe, linear_map.coe_mk,
    phi_map_eq, linear_map.comp_apply, ← ι_linear_equiv_apply_eq,
    ← ι_linear_equiv_symm_apply_eq, linear_equiv.apply_symm_apply,
    subtype.ext_iff, tensor_product.ext_iff, subtype.coe_mk],
  intros a b,
  rw [rmul_map_lmul_apply_apply, ← subtype.mem x, bimodule.lsmul_one, bimodule.rsmul_apply,
    one_mul],
end

noncomputable def phi_linear_equiv (hφ : φ.is_faithful_pos_map) :
  l(ℍ) ≃ₗ[ℂ] {x : l(ℍ ⊗[ℂ] ℍ) // x.is_bimodule_map} :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, phi_map_coe hφ x,
    inv_fun := λ x, phi_inv_map hφ x,
    left_inv := λ x, by simp only [← linear_map.comp_apply, phi_map_left_inverse,
      linear_map.one_apply, subtype.coe_mk],
    right_inv := λ x, by simp only [phi_map_right_inverse x, subtype.coe_eta],
    map_add' := λ x y, by simp only [map_add, subtype.coe_eta]; refl,
    map_smul' := λ r x, by { simp only [smul_hom_class.map_smul, ring_hom.id_apply], } },
end

lemma linear_equiv.comp_inj {R M₁ M₂ M₃ : Type*} [semiring R] [add_comm_monoid M₁]
  [add_comm_monoid M₂] [add_comm_monoid M₃] [module R M₁] [module R M₂] [module R M₃]
  (f : M₁ ≃ₗ[R] M₂) {x y : M₂ →ₗ[R] M₃} :
  x = y ↔ x ∘ₗ (f : M₁ →ₗ[R] M₂) = y ∘ₗ (f : M₁ →ₗ[R] M₂) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply],
  refine ⟨λ h a, by rw h, λ h a, _⟩,
  specialize h (f.symm a),
  simp_rw [linear_equiv.coe_coe, linear_equiv.apply_symm_apply] at h,
  exact h,
end

lemma phi_inv'_map_eq_phi_inv'_map :
  phi_inv_map hφ.elim = phi_inv'_map_coe hφ.elim :=
begin
  simp_rw [linear_equiv.comp_inj (phi_linear_equiv hφ.elim), phi_linear_equiv,
    linear_map.ext_iff, linear_map.comp_apply, linear_equiv.coe_coe,
    linear_equiv.coe_mk, ← linear_map.comp_apply, phi_map_left_inverse,
    phi_inv'_map_phi_map, eq_self_iff_true, forall_2_true_iff],
end

lemma sig_apply_sig_inv {t : ℝ} {x : ℍ} :
  hφ.elim.sig t (hφ.elim.sig (-t) x) = x :=
begin
  rw [sig_eq_iff_eq_sig_inv],
end
lemma sig_inv_apply_sig {t : ℝ} {x : ℍ} :
  hφ.elim.sig (-t) (hφ.elim.sig t x) = x :=
begin
  symmetry,
  rw [← sig_eq_iff_eq_sig_inv],
end

lemma rsmul_module_map_of_real_lsmul_module_map {n : Type*} [fintype n]
  {f : l(matrix n n ℂ)} (hf : ∀ a x : matrix n n ℂ, f (a ⬝ x) = a ⬝ f x)
  (a x : matrix n n ℂ) :
  f.real (a ⬝ x) = f.real a ⬝ x :=
begin
  simp_rw [linear_map.real_eq, star_eq_conj_transpose, conj_transpose_mul, hf, conj_transpose_mul,
    conj_transpose_conj_transpose],
end

lemma lsmul_module_map_iff_symm_eq_rsmul_module_map
  [hφ : fact φ.is_faithful_pos_map] {f : l(ℍ)} :
  f = rmul (f 1) ↔ linear_equiv.symm_map ℂ ℍ f = lmul (f 1) :=
begin
  rw [← linear_equiv.eq_symm_apply, linear_equiv.symm_map_symm_apply,
    @lmul_adjoint _ _ _ _ _ _ _ φ (λ x y, by simp only [star_eq_conj_transpose, mul_eq_mul];
      exact module.dual.is_faithful_pos_map.inner_eq x y),
    lmul_eq_mul, linear_map.mul_left_real, star_star, rmul_eq_mul],
  simp only [iff_self],
end

lemma linear_map.real_adjoint_eq (f : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ) :
  f.real.adjoint = (hφ.elim.sig (-1)).to_linear_map ∘ₗ f.adjoint.real ∘ₗ (hφ.elim.sig 1).to_linear_map :=
begin
  rw [linear_map.adjoint_real_eq],
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply,
    sig_inv_apply_sig, eq_self_iff_true, forall_true_iff],
end

lemma left_hand_twist_eq_sig_one :
  τ ∘ₗ (((η).adjoint ∘ₗ m) ⊗ₘ id) ∘ₗ υ⁻¹
    ∘ₗ (id ⊗ₘ ((tensor_product.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ))
    ∘ₗ υ ∘ₗ ((m).adjoint ⊗ₘ id) ∘ₗ (tensor_one_map : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ)
  = (hφ.elim.sig 1).to_linear_map :=
begin
  rw linear_map.ext_iff,
  intros x,
  simp only [linear_map.comp_apply, tensor_one_map_apply, tensor_product.map_tmul,
    linear_equiv.coe_coe, alg_equiv.to_linear_map_apply, linear_map.mul'_adjoint,
    one_apply, boole_mul, ite_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ,
    if_true, linear_map.one_apply],
  simp only [tensor_product.sum_tmul, map_sum, ← tensor_product.smul_tmul',
    smul_hom_class.map_smul, tensor_product.assoc_tmul, tensor_product.map_tmul,
    linear_equiv.coe_coe, tensor_product.comm_tmul, tensor_product.assoc_symm_tmul,
    tensor_product.lid_tmul, linear_map.comp_apply, linear_map.mul'_apply,
    linear_map.one_apply, nontracial.unit_adjoint_eq],
  have : ∀ i j : n, φ (std_basis_matrix i j 1 ⬝ x) = (x ⬝ φ.matrix) j i,
  { intros i j,
    rw [← star_one ℂ, ← std_basis_matrix_conj_transpose, ← module.dual.is_faithful_pos_map.inner_eq,
      inner_std_basis_matrix_left], },
  rw finset.sum_rotate,
  simp only [mul_eq_mul, this, smul_smul, ← finset.sum_smul, ← mul_apply],
  simp_rw [← smul_std_basis_matrix'],
  rw [← matrix_eq_sum_std_basis (φ.matrix⁻¹ ⬝ (x ⬝ _)), sig_one, matrix.mul_assoc],
end

lemma right_hand_twist_eq_sig_neg_one :
  τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ ((η).adjoint ∘ₗ m)) ∘ₗ υ
    ∘ₗ (((tensor_product.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ⊗ₘ id)
    ∘ₗ υ⁻¹ ∘ₗ (id ⊗ₘ (m).adjoint) ∘ₗ (one_tensor_map : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ)
  = (hφ.elim.sig (-1)).to_linear_map :=
begin
  rw linear_map.ext_iff,
  intros x,
  simp only [linear_map.comp_apply, one_tensor_map_apply, tensor_product.map_tmul,
    linear_equiv.coe_coe, alg_equiv.to_linear_map_apply, linear_map.mul'_adjoint,
    one_apply, boole_mul, ite_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ,
    if_true, linear_map.one_apply],
  simp only [tensor_product.tmul_sum, map_sum, ← tensor_product.smul_tmul, ← tensor_product.smul_tmul',
    smul_hom_class.map_smul, tensor_product.assoc_tmul, tensor_product.map_tmul,
    linear_equiv.coe_coe, tensor_product.comm_tmul, tensor_product.assoc_symm_tmul,
    tensor_product.lid_tmul, linear_map.comp_apply, linear_map.mul'_apply,
    linear_map.one_apply, nontracial.unit_adjoint_eq],
  have : ∀ i j : n, φ (x ⬝ std_basis_matrix i j 1) = (φ.matrix ⬝ x) j i,
  { intros i j,
    rw [← conj_transpose_conj_transpose x, ← module.dual.is_faithful_pos_map.inner_eq,
      ← inner_conj_symm, inner_std_basis_matrix_left, star_ring_end_apply, ← star_apply,
      star_eq_conj_transpose, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq], },
  simp only [mul_eq_mul, this, smul_smul, ← finset.sum_smul, ← mul_apply],
  simp_rw [← smul_std_basis_matrix', mul_comm, ← mul_apply],
  rw [← matrix_eq_sum_std_basis (φ.matrix ⬝ x ⬝ _), sig_neg_one],
end

lemma linear_functional_apply_sig (t : ℝ) (x : ℍ) :
  φ (hφ.elim.sig t x) = φ x :=
by rw [← alg_equiv.to_linear_map_apply, ← linear_map.comp_apply, linear_functional_comp_sig]

lemma balance_symm_1 :
  (η).adjoint ∘ₗ m ∘ₗ ((hφ.elim.sig 1).to_linear_map ⊗ₘ id)
    = (η).adjoint ∘ₗ m ∘ₗ (id ⊗ₘ (hφ.elim.sig (-1)).to_linear_map) :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  simp only [linear_map.comp_apply, tensor_product.map_tmul, linear_map.mul'_apply,
    nontracial.unit_adjoint_eq, linear_map.one_apply, alg_equiv.to_linear_map_apply],
  nth_rewrite 0 ← linear_functional_apply_sig (-1),
  rw [_root_.map_mul (hφ.elim.sig (-1)) _ b, sig_inv_apply_sig],
end
lemma balance_symm_2 :
  (η).adjoint ∘ₗ m ∘ₗ (id ⊗ₘ (hφ.elim.sig (-1)).to_linear_map)
    = (η).adjoint ∘ₗ m
      ∘ₗ ((tensor_product.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  simp only [linear_map.comp_apply, tensor_product.map_tmul,
    linear_map.mul'_apply, nontracial.unit_adjoint_eq, tensor_product.comm_tmul,linear_map.one_apply,
    linear_equiv.coe_coe, alg_equiv.to_linear_map_apply],
  calc φ (a ⬝ hφ.elim.sig (-1) b) = ⟪aᴴ, hφ.elim.sig (-1) b⟫_ℂ :
  by rw [module.dual.is_faithful_pos_map.inner_eq,
    conj_transpose_conj_transpose]
  ... = ⟪bᴴ, a⟫_ℂ : by rw [nontracial.inner_symm, module.dual.is_faithful_pos_map.sig_conj_transpose,
    sig_apply_sig_inv, conj_transpose_conj_transpose]
  ... = φ (b ⬝ a) : by rw [module.dual.is_faithful_pos_map.inner_eq, conj_transpose_conj_transpose],
end
