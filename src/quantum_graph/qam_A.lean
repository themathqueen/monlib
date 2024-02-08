/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.to_projections

/-!

# Single-edged quantum graphs

This file defines the single-edged quantum graph, and proves that it is a `QAM`.

-/

variables {n : Type*} [fintype n] [decidable_eq n]

open_locale tensor_product big_operators kronecker functional

local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

variables {φ : ℍ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map]

open_locale matrix

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ (matrix n n ℂ) _ _ _ x y

noncomputable def qam_A (hφ : φ.is_faithful_pos_map)
  (x : {x : ℍ // x ≠ 0}) : --(hx : x ≠ 0) :
  ℍ →ₗ[ℂ] ℍ :=
begin
  letI := fact.mk hφ,
  exact (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) • (linear_map.mul_left ℂ ((x : ℍ) ⬝ φ.matrix)
    * ((linear_map.mul_right ℂ (φ.matrix ⬝ (x : ℍ))).adjoint)),
end

lemma qam_A_eq (x : {x : ℍ // x ≠ 0}) :
  qam_A hφ.elim x = (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) • (linear_map.mul_left ℂ ((x : ℍ) ⬝ φ.matrix)
    * ((linear_map.mul_right ℂ (φ.matrix ⬝ (x : ℍ))).adjoint)) :=
rfl

lemma qam_A.to_matrix (x : {x : ℍ // x ≠ 0}) :
  hφ.elim.to_matrix (qam_A hφ.elim x)
    = (1 / ‖(x : ℍ)‖ ^ 2 : ℂ) • ((x : ℍ) ⬝ φ.matrix) ⊗ₖ
      (hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ (x : ℍ) ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2))ᴴᵀ :=
begin
  simp only [qam_A_eq, smul_hom_class.map_smul, alg_equiv.map_mul,
    linear_map.mul_left_to_matrix, linear_map.matrix.mul_right_adjoint,
    linear_map.mul_right_to_matrix, linear_map.is_faithful_pos_map.sig_apply_sig,
    matrix.conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq, matrix.mul_eq_mul,
    ← matrix.mul_kronecker_mul, matrix.one_mul, matrix.mul_one],
  have : (hφ.elim.sig (1 / 2 + -1)) ((x : ℍ)ᴴ ⬝ φ.matrix)
    = (hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ (x : ℍ) ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2))ᴴ :=
  calc (hφ.elim.sig (1 / 2 + -1)) ((x : ℍ)ᴴ ⬝ φ.matrix)
    = hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ (x : ℍ)ᴴ ⬝ φ.matrix
      ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)) :
  by simp only [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc]; norm_num
    ... = hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ (x : ℍ)ᴴ ⬝ hφ.elim.matrix_is_pos_def.rpow 1
      ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)) :
  by simp only [matrix.pos_def.rpow_one_eq_self]
    ... = (hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ (x : ℍ) ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2))ᴴ :
  by simp only [matrix.pos_def.rpow_mul_rpow, matrix.conj_transpose_mul,
    (matrix.pos_def.rpow.is_hermitian _ _).eq, matrix.mul_assoc]; norm_num,
  simp only [this],
  refl,
end

@[instance] private def has_smul.units_matrix_ne_zero :
  has_smul ℂˣ {x : matrix n n ℂ // x ≠ 0} :=
{smul := λ α x, (⟨((α : ℂ) • (x : matrix n n ℂ) : matrix n n ℂ), smul_ne_zero (units.ne_zero α)
  (set.mem_set_of.mp (subtype.mem x))⟩ : {x : matrix n n ℂ // x ≠ 0})}

private lemma has_smul.units_matrix_ne_zero_coe
  (x : {x : matrix n n ℂ // x ≠ 0}) (α : ℂˣ) :
  ((α • x : {x : matrix n n ℂ // x ≠ 0}) : matrix n n ℂ) = (α : ℂ) • x :=
rfl

open matrix

/-- given a non-zero matrix $x$, we always get $A(x)$ is non-zero -/
lemma qam_A.ne_zero (x : {x : matrix n n ℂ // x ≠ 0}) :
  qam_A hφ.elim x ≠ 0 :=
begin
  have hx := set.mem_set_of.mp (subtype.mem x),
  simp_rw [ne.def, qam_A, smul_eq_zero, div_eq_zero_iff, one_ne_zero, false_or,
    sq_eq_zero_iff, complex.of_real_eq_zero, norm_eq_zero', hx, false_or,
    ← rank_one_to_matrix_transpose_Psi_symm, ← one_map_transpose_symm_eq,
    linear_equiv.map_eq_zero_iff, star_alg_equiv.map_eq_zero_iff,
    alg_equiv.map_eq_zero_iff, continuous_linear_map.coe_eq_zero,
    rank_one.eq_zero_iff, or_self, hx, not_false_iff],
end

/-- Given any non-zero matrix $x$ and non-zero $\alpha\in\mathbb{C}$ we have
  $$A(\alpha x)=A(x),$$
  in other words, it is not injective. However, it `is_almost_injective` (see `qam_A.is_almost_injective`). -/
lemma qam_A.smul (x : {x : matrix n n ℂ // x ≠ 0}) (α : ℂˣ) :
  qam_A hφ.elim (α • x) = qam_A hφ.elim x :=
begin
  simp_rw [qam_A, has_smul.units_matrix_ne_zero_coe, norm_smul, smul_mul,
    matrix.mul_smul, linear_map.mul_right_smul, linear_map.adjoint_smul,
    linear_map.mul_left_smul, smul_mul_smul, smul_smul, complex.mul_conj,
    complex.of_real_mul, mul_pow, ← one_div_mul_one_div_rev, mul_assoc, ← complex.of_real_pow,
    complex.norm_sq_eq_abs, ← complex.norm_eq_abs],
  rw [one_div_mul_cancel, mul_one],
  { simp_rw [ne.def, complex.of_real_eq_zero, sq_eq_zero_iff, norm_eq_zero],
    exact units.ne_zero _, },
end

private lemma kronecker_to_tensor_product_mul' (x y : matrix (n × n) (n × n) ℂ) :
  (x * y).kronecker_to_tensor_product
    = x.kronecker_to_tensor_product * y.kronecker_to_tensor_product :=
calc (x * y).kronecker_to_tensor_product = kronecker_to_tensor (x * y) : rfl
  ... = kronecker_to_tensor x * kronecker_to_tensor y : _root_.map_mul _ _ _
  ... = x.kronecker_to_tensor_product * y.kronecker_to_tensor_product : rfl

lemma qam_A.is_idempotent (x : {x : matrix n n ℂ // x ≠ 0}) :
  qam.refl_idempotent hφ.elim (qam_A hφ.elim x) (qam_A hφ.elim x) = qam_A hφ.elim x :=
begin
  rw [← function.injective.eq_iff (hφ.elim.Psi 0 (1/2)).injective,
    Psi.refl_idempotent, qam_A],
  simp only [← rank_one_to_matrix_transpose_Psi_symm],
  simp_rw [smul_hom_class.map_smul, linear_equiv.apply_symm_apply, smul_mul_smul,
    ← one_map_transpose_symm_eq, ← _root_.map_mul, ← rank_one_lm_eq_rank_one,
    linear_map.mul_eq_comp, rank_one_lm_comp_rank_one_lm, smul_hom_class.map_smul,
    inner_self_eq_norm_sq_to_K, smul_smul, mul_assoc],
  rw [one_div_mul_cancel, mul_one],
  { simp_rw [ne.def, sq_eq_zero_iff, complex.of_real_eq_zero, norm_eq_zero],
    exact subtype.mem x, },
end

lemma Psi.one :
  hφ.elim.Psi 0 (1/2) 1
    = (tensor_product.map (1 : l(ℍ)) (transpose_alg_equiv n ℂ ℂ).to_linear_map)
      (hφ.elim.to_matrix
        (|φ.matrix⁻¹⟩⟨φ.matrix⁻¹|)).kronecker_to_tensor_product :=
begin
  nth_rewrite_lhs 0 ← rank_one.sum_orthonormal_basis_eq_id_lm (@linear_map.is_faithful_pos_map.orthonormal_basis n _ _ φ _),
  apply_fun (one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) using (star_alg_equiv.injective _),
  ext1,
  simp_rw [← one_map_transpose_symm_eq, star_alg_equiv.apply_symm_apply, map_sum,
    linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply, op, linear_equiv.coe_coe,
    mul_opposite.coe_op_linear_equiv, one_map_transpose_apply, rank_one_to_matrix,
    conj_transpose_col, ← vec_mul_vec_eq, vec_mul_vec_apply, matrix.sum_apply, kronecker_map,
    of_apply, linear_map.is_faithful_pos_map.sig_zero, pi.star_apply,
    transpose_apply, conj_transpose_apply, reshape_apply,
    linear_map.is_faithful_pos_map.orthonormal_basis_apply,
    sig_apply_matrix_mul_pos_def, ← pos_def.rpow_neg_one_eq_inv_self hφ.elim.matrix_is_pos_def,
    pos_def.rpow_mul_rpow, mul_apply, std_basis_matrix, boole_mul, mul_boole, ite_and],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq,
    finset.mem_univ, if_true],
  simp only [star_ite, star_zero, mul_ite, ite_mul, zero_mul, mul_zero],
  have : ∀ a b c d : n, (a,b) = (c,d) ↔ (a = c ∧ b = d) := λ _ _ _ _, prod.eq_iff_fst_eq_snd_eq,
  simp_rw [← ite_and, ← this, prod.mk.eta, finset.sum_ite_eq', finset.mem_univ, if_true,
    ← conj_transpose_apply, (pos_def.rpow.is_hermitian _ _).eq],
  rw [mul_comm],
  norm_num,
end

lemma one_map_transpose_Psi_eq (A : l(ℍ)) :
  (tensor_product.map (1 : l(ℍ)) (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
    (hφ.elim.Psi 0 (1/2) A)
  = (tensor_product.map A (1 : l(ℍ)))
    (hφ.elim.to_matrix
      (|φ.matrix⁻¹⟩⟨φ.matrix⁻¹|)).kronecker_to_tensor_product :=
begin
  have := calc ∑ k l, (|A (e_{k,l} ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)))⟩⟨e_{k,l}
    ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2))| : l(ℍ))
    = A ∘ₗ (∑ k l, (|(e_{k,l} ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)))⟩⟨e_{k,l}
      ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2))| : l(ℍ))) :
  by { simp_rw [← linear_map.comp_rank_one, ← linear_map.comp_sum], }
    ... = A ∘ₗ 1 : by { simp_rw [← finset.sum_product',
      ← linear_map.is_faithful_pos_map.orthonormal_basis_apply, finset.univ_product_univ, rank_one.sum_orthonormal_basis_eq_id_lm], }
    ... = A : by rw linear_map.comp_one,
  nth_rewrite_lhs 0 ← this,
  simp_rw [map_sum, linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply],
  have : ∀ x x_1, (hφ.elim.sig 0)
    (A (std_basis_matrix x x_1 1 ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1 / 2))))
    = A ((hφ.elim.sig 0)
      (std_basis_matrix x x_1 1 ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1 / 2)))),
  { intros x x_1,
    simp_rw [hφ.elim.sig_zero], },
  simp_rw [this, tensor_product.map_tmul, linear_map.one_apply, ← tensor_product.map_tmul A,
    ← linear_map.is_faithful_pos_map.Psi_to_fun'_apply, ← map_sum, ← finset.sum_product',
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply,
    finset.univ_product_univ, rank_one.sum_orthonormal_basis_eq_id_lm],
  have := @Psi.one n _ _ φ hφ,
  rw [linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk] at this,
  simp_rw [this, ← one_map_transpose_symm_eq],
  have : ∀ x, (tensor_product.map A (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
    ((one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm x)
    = (tensor_product.map A (1 : l(ℍ))) x.kronecker_to_tensor_product,
  { intros x,
    rw kmul_representation x,
    simp_rw [map_sum, smul_hom_class.map_smul, one_map_transpose_symm_eq,
      kronecker_to_tensor_product_apply, tensor_product.map_tmul, linear_map.one_apply,
      alg_equiv.to_linear_map_apply, alg_equiv.symm_apply_apply], },
  simp_rw [this],
end

lemma qam_A.is_real (x : {x : ℍ // x ≠ 0}) :
  (qam_A hφ.elim x).is_real :=
begin
  simp_rw [linear_map.is_real_iff, qam_A, linear_map.real_smul, linear_map.mul_eq_comp,
    linear_map.real_comp, linear_map.matrix.mul_right_adjoint, linear_map.mul_right_real,
    linear_map.mul_left_real, ← linear_map.mul_eq_comp,
    ← (linear_map.commute_mul_left_right _ _).eq, conj_transpose_mul,
    hφ.elim.matrix_is_pos_def.1.eq, sig_apply_matrix_mul_pos_def',
    star_eq_conj_transpose, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq,
    conj_transpose_conj_transpose, star_ring_end_apply, star_div', star_one,
    complex.star_def, ← complex.of_real_pow, complex.conj_of_real],
end

private lemma qam_A_is_sa_iff_aux [hφ : fact φ.is_faithful_pos_map] (x : ℍ) :
  (|φ.matrix ⬝ x⟩⟨φ.matrix ⬝ x| : l(ℍ))
    = linear_map.mul_left ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ))
      ∘ₗ linear_map.mul_left ℂ φ.matrix :=
begin
  calc (|(φ.matrix ⬝ x)⟩⟨(φ.matrix ⬝ x)| : l(ℍ))
    = linear_map.mul_left ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ))
      ∘ₗ ((linear_map.mul_left ℂ φ.matrix).adjoint) :
  by { simp only [linear_map.comp_rank_one, linear_map.rank_one_comp',
    linear_map.mul_left_apply, mul_eq_mul], }
  ... = linear_map.mul_left ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ))
    ∘ₗ linear_map.mul_left ℂ φ.matrix :
  by { simp_rw [linear_map.matrix.mul_left_adjoint, hφ.elim.matrix_is_pos_def.1.eq], },
end
private lemma qam_A_is_sa_iff_aux2 [hφ : fact φ.is_faithful_pos_map] (x : ℍ) :
  (|x ⬝ φ.matrix⟩⟨φ.matrix ⬝ x| : l(ℍ))
    = (linear_map.mul_right ℂ φ.matrix) ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ
      linear_map.mul_left ℂ φ.matrix :=
begin
  calc (|x ⬝ φ.matrix⟩⟨φ.matrix ⬝ x| : l(ℍ))
    = (linear_map.mul_right ℂ φ.matrix) ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ
      ((linear_map.mul_left ℂ φ.matrix).adjoint) :
  by { simp only [linear_map.comp_rank_one, linear_map.rank_one_comp',
    linear_map.mul_left_apply, linear_map.mul_right_apply, mul_eq_mul], }
  ... = linear_map.mul_right ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ
    (linear_map.mul_left ℂ φ.matrix) :
  by { simp_rw [linear_map.matrix.mul_left_adjoint, hφ.elim.matrix_is_pos_def.1.eq], },
end
private lemma qam_A_is_sa_iff_aux3 [hφ : fact φ.is_faithful_pos_map]
  (x : {x : ℍ // x ≠ 0}) (h : ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ
    • (φ.matrix * (x : ℍ)ᴴ) = ⟪↑x, (x : ℍ)ᴴ⟫_ℂ • ((x : ℍ) * φ.matrix)) :
  ⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ ≠ 0 :=
begin
  simp_rw [ne.def, div_eq_zero_iff, inner_self_eq_zero, ← star_eq_conj_transpose,
    star_eq_zero, (set.mem_set_of.mp (subtype.mem x)), or_false, star_eq_conj_transpose],
  intros h',
  simp_rw [h', zero_smul, smul_eq_zero, inner_self_eq_zero, ← star_eq_conj_transpose,
    star_eq_zero, set.mem_set_of.mp (subtype.mem x), false_or] at h,
  letI := hφ.elim.matrix_is_pos_def.invertible,
  have : linear_map.mul_left ℂ φ.matrix (star (x : ℍ)) = linear_map.mul_left ℂ φ.matrix 0,
  { simp_rw [linear_map.mul_left_apply, h, mul_zero], },
  simp_rw [linear_map.mul_left_inj φ.matrix, star_eq_zero,
    (set.mem_set_of.mp (subtype.mem x))] at this,
  exact this,
end
private lemma qam_A_is_sa_iff_aux4 [hφ : fact φ.is_faithful_pos_map] (x : {x : ℍ // x ≠ 0})
  (h : ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ
    • (φ.matrix * (x : ℍ)ᴴ) = ⟪↑x, (x : ℍ)ᴴ⟫_ℂ • (↑x * φ.matrix)) :
  (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • hφ.elim.sig 1 (x : ℍ)
    = (x : ℍ)ᴴ :=
begin
  letI := hφ.elim.matrix_is_pos_def.invertible,
  calc (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • hφ.elim.sig 1 (x : ℍ)
      = (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • φ.matrix⁻¹ ⬝ ↑x ⬝ φ.matrix :
  by { simp_rw [hφ.elim.sig_apply, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self], }
    ... = ((1 / ⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • φ.matrix⁻¹) ⬝
      (⟪↑x, (x : ℍ)ᴴ⟫_ℂ • (↑x ⬝ φ.matrix)) :
  by { simp only [matrix.mul_smul, matrix.smul_mul, smul_smul, matrix.mul_assoc,
    mul_comm (1 / _ : ℂ), mul_one_div], }
    ... = ((1 / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • φ.matrix⁻¹) ⬝
      (⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ • (φ.matrix ⬝ (↑x)ᴴ)) :
  by { simp_rw [← mul_eq_mul, ← h], }
    ... = (⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • (φ.matrix⁻¹ ⬝ φ.matrix ⬝ (↑x)ᴴ) :
  by { simp_rw [← mul_eq_mul, smul_mul_smul, mul_assoc, mul_comm (1 / _ : ℂ),
    mul_one_div], }
    ... = (x : ℍ)ᴴ :
  by { rw [div_self, one_smul, matrix.mul_assoc, inv_mul_cancel_left_of_invertible],
    simp_rw [ne.def, inner_self_eq_zero, ← star_eq_conj_transpose, star_eq_zero],
    exact subtype.mem x, },
end

lemma sig_eq_lmul_rmul (t : ℝ) :
  (hφ.elim.sig t).to_linear_map
    = linear_map.mul_left ℂ (hφ.elim.matrix_is_pos_def.rpow (-t))
      ∘ₗ linear_map.mul_right ℂ (hφ.elim.matrix_is_pos_def.rpow t) :=
begin
  rw linear_map.ext_iff,
  intros a,
  simp_rw [alg_equiv.to_linear_map_apply, hφ.elim.sig_apply, linear_map.comp_apply,
    linear_map.mul_left_apply, linear_map.mul_right_apply, ← mul_assoc, mul_eq_mul],
end

private lemma qam_A_is_sa_iff_aux5 (x : {x : ℍ // x ≠ 0})
  (h : (linear_map.mul_left ℂ φ.matrix).comp (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ))
    = (linear_map.mul_right ℂ φ.matrix).comp (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ))) :
  qam.symm hφ.elim (|(x : ℍ)⟩⟨(x : ℍ)|) = (|(x : ℍ)⟩⟨(x : ℍ)|) :=
begin
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  calc qam.symm hφ.elim (|(x : ℍ)⟩⟨(x : ℍ)|)
    = (hφ.elim.sig (-1)).to_linear_map ∘ₗ (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ)) : _
  ... = (linear_map.mul_left ℂ φ.matrix) ∘ₗ (linear_map.mul_right ℂ φ.matrix⁻¹)
    ∘ₗ (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ)) : _
  ... = (linear_map.mul_right ℂ (φ.matrix⁻¹ : ℍ)) ∘ₗ (linear_map.mul_right ℂ φ.matrix)
    ∘ₗ (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ)) : _
  ... = (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ)) : _,
  { simp_rw [qam.rank_one.symmetric_eq, linear_map.comp_rank_one,
      alg_equiv.to_linear_map_apply], },
  { simp_rw [sig_eq_lmul_rmul, neg_neg, pos_def.rpow_one_eq_self,
      pos_def.rpow_neg_one_eq_inv_self, linear_map.comp_assoc], },
  { simp_rw [← linear_map.mul_eq_comp, ← mul_assoc, (linear_map.commute_mul_left_right _ _).eq,
      mul_assoc, linear_map.mul_eq_comp, h], },
  { rw [← linear_map.comp_assoc, ← linear_map.mul_right_mul, mul_eq_mul, mul_inv_of_invertible,
      linear_map.mul_right_one, linear_map.id_comp], },
end

lemma sig_comp_eq_iff_eq_sig_inv_comp (r : ℝ) (a b : l(ℍ)) :
  (hφ.elim.sig r).to_linear_map.comp a = b
    ↔ a = (hφ.elim.sig (-r)).to_linear_map.comp b :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply],
  split; intros h x,
  { simp_rw [← h, alg_equiv.to_linear_map_apply, hφ.elim.sig_apply_sig, neg_add_self, hφ.elim.sig_zero], },
  { simp_rw [h, alg_equiv.to_linear_map_apply, hφ.elim.sig_apply_sig,
      add_neg_self, hφ.elim.sig_zero], },
end
lemma sig_eq_iff_eq_sig_inv (r : ℝ) (a b : ℍ) :
  hφ.elim.sig r a = b ↔ a = hφ.elim.sig (-r) b :=
begin
  split; rintros rfl;
  simp only [hφ.elim.sig_apply_sig, neg_add_self, add_neg_self, hφ.elim.sig_zero],
end
lemma comp_sig_eq_iff_eq_comp_sig_inv (r : ℝ) (a b : l(ℍ)) :
  a.comp (hφ.elim.sig r).to_linear_map = b ↔ a = b.comp (hφ.elim.sig (-r)).to_linear_map :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply],
  split; intros h x,
  { simp only [← h, alg_equiv.to_linear_map_apply, hφ.elim.sig_apply_sig, add_neg_self, hφ.elim.sig_zero], },
  { simp only [h, hφ.elim.sig_apply_sig, neg_add_self, hφ.elim.sig_zero, alg_equiv.to_linear_map_apply], },
end

private lemma qam_A_is_sa_iff_aux_aux6 (r : ℝ) (a b : ℍ) :
  ⟪hφ.elim.sig r a, b⟫_ℂ
    = ⟪hφ.elim.sig (r/2) a, hφ.elim.sig (r/2) b⟫_ℂ :=
begin
  simp_rw ← alg_equiv.to_linear_map_apply,
  nth_rewrite_rhs 1 ← linear_map.is_faithful_pos_map.sig_adjoint,
  simp_rw [linear_map.adjoint_inner_right, alg_equiv.to_linear_map_apply,
    linear_map.is_faithful_pos_map.sig_apply_sig hφ.elim, add_halves],
end

private lemma qam_A_is_sa_iff_aux2_aux6 (x : ℍ) (α : nnrealˣ)
  (h : hφ.elim.sig 1 x = (((α : nnreal) : ℝ) : ℂ) • x) :
  x ⬝ φ.matrix = (((α : nnreal) : ℝ) : ℂ) • φ.matrix ⬝ x :=
begin
  have hα : (((α : nnreal) : ℝ) : ℂ) ≠ 0 := by { norm_cast, exact units.ne_zero α, },
  letI gg : no_zero_smul_divisors ℂ ℍ := module.free.no_zero_smul_divisors ℂ ℍ,
  have h' := h,
  rw [sig_eq_iff_eq_sig_inv, smul_hom_class.map_smul] at h,
  have h'' : x = (((α : nnreal)⁻¹ : ℝ) : ℂ) • hφ.elim.sig 1 x,
  { rw [h', smul_smul, complex.of_real_inv, inv_mul_cancel hα, one_smul], },
  symmetry,
  calc (((α : nnreal) : ℝ) : ℂ) • φ.matrix ⬝ x = φ.matrix ⬝ ((((α : nnreal) : ℝ) : ℂ) • x) :
  by { simp_rw [matrix.mul_smul], }
  ... = φ.matrix ⬝ (hφ.elim.sig 1 x) : by rw ← h'
  ... = x ⬝ φ.matrix : _,
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [linear_map.is_faithful_pos_map.sig_apply hφ.elim,
    pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self,
    matrix.mul_assoc, mul_inv_cancel_left_of_invertible],
end

private lemma qam_A_is_sa_iff_aux3_aux6 (x : ℍ) (α : nnrealˣ)
  (H : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = |hφ.elim.sig 1 x⟩⟨x|)
  (h : hφ.elim.sig 1 x = (((α : nnreal) : ℝ) : ℂ) • x) :
  |(real.sqrt ((α : nnreal) : ℝ) : ℂ) • x⟩⟨(real.sqrt ((α : nnreal) : ℝ) : ℂ) • x| = |xᴴ⟩⟨xᴴ| :=
begin
  have : 0 ≤ ((α : nnreal) : ℝ) := nnreal.coe_nonneg _,
  rw [← continuous_linear_map.coe_inj, rank_one.smul_real_apply, rank_one.apply_smul, smul_smul,
    ← complex.of_real_mul, ← real.sqrt_mul this, real.sqrt_mul_self this,
    ← rank_one.apply_smul, ← h, ← H],
end

private lemma qam_A_is_sa_iff_aux4_aux6 (x' : {x : ℍ // x ≠ 0})
  (this :  ⟪(x' : ℍ), (x' : ℍ)⟫_ℂ • hφ.elim.sig 1 (x' : ℍ)
    = ⟪hφ.elim.sig 1 (x' : ℍ), (x' : ℍ)⟫_ℂ • (x' : ℍ)) :
  ∃ α : nnrealˣ, hφ.elim.sig 1 (x' : ℍ) = (((α : nnreal) : ℝ) : ℂ) • (x' : ℍ) :=
begin
  let x : ℍ := (x' : ℍ),
  have hx : x ≠ 0 := set.mem_set_of.mp (subtype.mem x'),
  let α : ℝ := (‖hφ.elim.sig (1/2) x‖ ^ 2) / (‖x‖ ^ 2),
  have hα' : 0 ≤ α,
  { simp_rw [α],
    exact div_nonneg (sq_nonneg _) (sq_nonneg _), },
  let α' : nnreal := ⟨α, hα'⟩,
  have hα : α' ≠ 0,
  { simp_rw [α', ← nnreal.coe_ne_zero, ne.def, nnreal.coe_mk, div_eq_zero_iff,
      sq_eq_zero_iff, norm_eq_zero, sig_eq_iff_eq_sig_inv, map_zero, or_self],
    exact hx, },
  existsi units.mk0 α' hα,
  simp_rw [units.coe_mk0, α', nnreal.coe_mk, complex.of_real_div],
  symmetry,
  calc (((‖(hφ.elim.sig (1 / 2)) x‖ ^ 2 : ℝ) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ)) • x
    = (1 / (‖x‖ ^ 2 : ℂ)) • ((‖hφ.elim.sig (1/2) x‖ ^ 2 : ℂ) • x) :
  by { simp_rw [smul_smul, mul_comm (1 / _ : ℂ), mul_one_div, complex.of_real_pow], }
  ... = (1 / ⟪x, x⟫_ℂ)
    • (⟪hφ.elim.sig (1/2) x, hφ.elim.sig (1/2) x⟫_ℂ • x) :
  by { simp_rw [inner_self_eq_norm_sq_to_K], }
  ... = (1 / ⟪x, x⟫_ℂ) • (⟪hφ.elim.sig 1 x, x⟫_ℂ • x) :
  by { rw [← qam_A_is_sa_iff_aux_aux6], }
  ... = (1 / ⟪x, x⟫_ℂ) • (⟪x, x⟫_ℂ • hφ.elim.sig 1 x) :
  by { rw [← this], }
  ... = hφ.elim.sig 1 x : _,
  rw [smul_smul, one_div, inv_mul_cancel, one_smul],
  exact inner_self_ne_zero.mpr hx,
end

lemma sig_eq_self_iff_commute (x : ℍ) :
  hφ.elim.sig 1 x = x ↔ commute φ.matrix x :=
begin
  simp_rw [hφ.elim.sig_apply, commute, semiconj_by, mul_eq_mul,
    pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self],
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  split; intros h,
  { nth_rewrite_lhs 0 [← h],
    rw [matrix.mul_assoc, mul_inv_cancel_left_of_invertible], },
  { rw [matrix.mul_assoc, ← h, ← matrix.mul_assoc, inv_mul_of_invertible, matrix.one_mul], },
end


private lemma qam_A_is_sa_iff_aux7 (x : {x : ℍ // x ≠ 0}) (α : nnrealˣ) (β : ℂˣ)
  (hx : (x : ℍ) = (star (β : ℂ) * (real.sqrt ((α : nnreal) : ℝ) : ℂ)) • (x : ℍ)ᴴ)
  (hx2 : (x : ℍ) = ((β⁻¹ : ℂ) * (((real.sqrt ((α : nnreal) : ℝ))⁻¹ : ℝ) : ℂ)) • (x : ℍ)ᴴ) :
  ‖(β : ℂ)‖ ^ 2 * ((α : nnreal) : ℝ) = 1 :=
begin
  have : (x : ℍ) - (x : ℍ) = 0 := sub_self _,
  nth_rewrite 0 hx at this,
  nth_rewrite 1 hx2 at this,
  simp_rw [← sub_smul, smul_eq_zero, ← star_eq_conj_transpose, star_eq_zero,
    set.mem_set_of.mp (subtype.mem x), or_false, sub_eq_zero, complex.of_real_inv,
    ← mul_inv] at this,
  have hi : 0 ≤ ((α : nnreal) : ℝ) := nnreal.coe_nonneg _,
  rw [← mul_inv_eq_one₀, inv_inv, mul_mul_mul_comm, complex.star_def,
    ← complex.norm_sq_eq_conj_mul_self, complex.norm_sq_eq_abs, ← complex.norm_eq_abs,
    ← complex.of_real_mul, ← real.sqrt_mul hi, real.sqrt_mul_self hi, ← complex.of_real_mul,
    complex.of_real_eq_one] at this,
  exact this,
  simp_rw [ne.def, inv_eq_zero, mul_eq_zero, complex.of_real_eq_zero, real.sqrt_eq_zero hi,
    nnreal.coe_eq_zero, units.ne_zero, or_false, not_false_iff],
end

private lemma qam_A_is_sa_iff_aux8 (α : nnrealˣ) (β : ℂˣ) (h : ‖(β : ℂ)‖ ^ 2 * ((α : nnreal) : ℝ) = 1) :
  ∃ γ : ℂˣ, (γ : ℂ) ^ 2 = (β : ℂ) * (((α : nnreal) : ℝ).sqrt : ℂ)
    ∧ ‖(γ : ℂ)‖ ^ 2 = 1 ∧ star (γ : ℂ) = (γ : ℂ)⁻¹ :=
begin
  let γ : ℂ := ((β : ℂ) * (((α : nnreal) : ℝ).sqrt : ℂ)) ^ (((2 : ℕ) : ℂ)⁻¹),
  have hγ : γ ≠ 0,
  { simp only [ne.def, γ, complex.cpow_eq_zero_iff, ne.def, inv_eq_zero, units.mul_right_eq_zero,
      complex.of_real_eq_zero, real.sqrt_eq_zero, nnreal.zero_le_coe, nnreal.coe_eq_zero,
      units.ne_zero, not_false_iff, false_and], },
  have : γ ^ 2 = (β : ℂ) * (((α : nnreal) : ℝ).sqrt : ℂ),
  { simp_rw [γ, complex.cpow_nat_inv_pow _ (two_ne_zero)], },
  have this1 : ‖γ‖ ^ 2 = 1,
  { rw [← sq_eq_sq (sq_nonneg (‖γ‖)) (zero_le_one' ℝ), ← norm_pow, this,
      norm_mul, mul_pow, is_R_or_C.norm_of_real, abs_of_nonneg (real.sqrt_nonneg _),
      real.sq_sqrt (nnreal.coe_nonneg _), h, one_pow], },
  refine ⟨units.mk0 γ hγ, this, this1, _⟩,
  rw [complex.norm_eq_abs, ← complex.of_real_inj, ← complex.norm_sq_eq_abs,
    ← complex.mul_conj, complex.of_real_one, star_ring_end_apply, mul_comm,
    mul_eq_one_iff_eq_inv₀ hγ] at this1,
  exact this1,
end

private lemma qam_A_is_sa_iff_aux9 (x : ℍ) (α : nnrealˣ) (β γ : ℂˣ)
  (h : (γ : ℂ) ^ 2 = (β : ℂ) * (((α : nnreal) : ℝ).sqrt : ℂ))
  (h2 : star (γ : ℂ) = (γ : ℂ)⁻¹)
  (hx : xᴴ = ((β : ℂ) * (real.sqrt ((α : nnreal) : ℝ) : ℂ)) • x) :
  x.is_almost_hermitian :=
begin
  refine ⟨units.mk0 (star (γ : ℂ)) (star_ne_zero.mpr (units.ne_zero _)),
    (γ : ℂ) • x, _⟩,
  simp_rw [is_hermitian, conj_transpose_smul, h2, units.coe_mk0, smul_smul,
    inv_mul_cancel (units.ne_zero γ), one_smul, eq_self_iff_true, true_and],
  rw [eq_comm, eq_inv_smul_iff₀ (units.ne_zero γ), smul_smul, ← sq, h],
  exact hx.symm,
end

private lemma qam_A_is_sa_iff_aux5_aux6 (x' : {x : ℍ // x ≠ 0})
  (this :  ⟪(x' : ℍ), (x' : ℍ)⟫_ℂ • hφ.elim.sig 1 (x' : ℍ)
    = ⟪hφ.elim.sig 1 (x' : ℍ), (x' : ℍ)⟫_ℂ • (x' : ℍ))
  (h : qam.symm hφ.elim (|(x' : ℍ)⟩⟨(x' : ℍ)|) = (|(x' : ℍ)⟩⟨(x' : ℍ)|))
  (hh : (x' : ℍ).is_almost_hermitian) :
  commute φ.matrix x' :=
begin
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this,
  have : hφ.elim.sig (-1) (x' : ℍ)ᴴ = (((α : nnreal) : ℝ) : ℂ) • (x' : ℍ)ᴴ,
  { rw [← linear_map.is_faithful_pos_map.sig_conj_transpose, hα,
      conj_transpose_smul, complex.star_def, complex.conj_of_real], },
  rw [qam.rank_one.symmetric_eq, this] at h,
  obtain ⟨β, y, hβy, hy⟩ := hh,
  have this1 : y ≠ 0,
  { intros H,
    rw [H, smul_zero, eq_comm] at hβy,
    exact set.mem_set_of.mp (subtype.mem x') hβy, },
  have Hβ : β ≠ 0,
  { intros hβ,
    rw [hβ, zero_smul, eq_comm] at hβy,
    exact set.mem_set_of.mp (subtype.mem x') hβy, },
  simp_rw [← hβy, conj_transpose_smul, hy.eq, ← rank_one_lm_eq_rank_one, smul_smul,
    rank_one_lm_smul, smul_rank_one_lm, smul_smul] at h,
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, rank_one_lm_eq_rank_one,
    continuous_linear_map.coe_eq_zero, rank_one.eq_zero_iff, or_self,
    complex.star_def, star_ring_end_self_apply, ← complex.norm_sq_eq_conj_mul_self,
    mul_rotate', ← complex.norm_sq_eq_conj_mul_self, mul_comm, ← mul_sub_one,
    mul_eq_zero, complex.of_real_eq_zero, complex.norm_sq_eq_zero] at h,
  simp_rw [this1, Hβ, false_or, or_false, sub_eq_zero] at h,
  rw [h, one_smul, sig_eq_self_iff_commute] at hα,
  exact hα,
end

private lemma qam_A_is_sa_iff_aux6 (x' : {x : ℍ // x ≠ 0})
  (h : qam.symm hφ.elim (|(x' : ℍ)⟩⟨(x' : ℍ)|) = (|(x' : ℍ)⟩⟨(x' : ℍ)|)) :
  (x' : ℍ).is_almost_hermitian ∧ commute φ.matrix x' :=
begin
  let x : ℍ := (x' : ℍ),
  have hx : x ≠ 0 := set.mem_set_of.mp (subtype.mem x'),
  have h' := (qam.symm_iff_symm' _ _).mp h,
  have H : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|hφ.elim.sig 1 x⟩⟨x| : l(ℍ)),
  { rw [← alg_equiv.to_linear_map_apply, ← linear_map.comp_rank_one, ← neg_neg (1 : ℝ),
      ← sig_comp_eq_iff_eq_sig_inv_comp, linear_map.comp_rank_one],
    rw qam.rank_one.symmetric_eq at h,
    exact h, },
  have H' : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|x⟩⟨hφ.elim.sig 1 x| : l(ℍ)),
  { simp_rw [← alg_equiv.to_linear_map_apply],
    rw [← linear_map.is_faithful_pos_map.sig_adjoint,
      ← linear_map.rank_one_comp, ← neg_neg (1 : ℝ),
      ← comp_sig_eq_iff_eq_comp_sig_inv],
    have : (|xᴴ⟩⟨xᴴ| : l(ℍ)) ∘ₗ (hφ.elim.sig (-1)).to_linear_map
      = |xᴴ⟩⟨(hφ.elim.sig (-1)).to_linear_map.adjoint xᴴ|,
    { exact linear_map.rank_one_comp _ _ _, },
    rw [this, linear_map.is_faithful_pos_map.sig_adjoint],
    rw qam.rank_one.symmetric'_eq at h',
    exact h', },
  have : (|hφ.elim.sig 1 x⟩⟨x| : l(ℍ)) = |x⟩⟨hφ.elim.sig 1 x|,
  { rw [← H, ← H'], },
  simp_rw [continuous_linear_map.coe_inj, continuous_linear_map.ext_iff,
    rank_one_apply] at this,
  specialize this x,
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this,
  have hα' := (qam_A_is_sa_iff_aux3_aux6 _ α H hα).symm,
  have hα'' := qam_A_is_sa_iff_aux2_aux6 _ _ hα,
  obtain ⟨β, hβ⟩ := rank_one.ext_iff _ _ hα',
  rw [smul_smul] at hβ,
  have hβ' : (x : ℍ) = (star (β : ℂ) * (real.sqrt ((α : nnreal) : ℝ) : ℂ)) • (x : ℍ)ᴴ,
  { rw ← function.injective.eq_iff (conj_transpose_add_equiv n n ℂ).injective,
    simp_rw [conj_transpose_add_equiv_apply, conj_transpose_smul, star_mul', star_star,
      complex.star_def, complex.conj_of_real, conj_transpose_conj_transpose],
    exact hβ, },
  have hβ'' : (x : ℍ) = ((β⁻¹ : ℂ) * (((real.sqrt ((α : nnreal) : ℝ))⁻¹ : ℝ) : ℂ)) • (x : ℍ)ᴴ,
  { rw [hβ, smul_smul, mul_mul_mul_comm, inv_mul_cancel (units.ne_zero β), one_mul,
      ← complex.of_real_mul, inv_mul_cancel, complex.of_real_one, one_smul],
    simp_rw [real.sqrt_ne_zero (nnreal.coe_nonneg _), nnreal.coe_ne_zero],
    exact units.ne_zero _, },
  have Hβ := qam_A_is_sa_iff_aux7 x' α β hβ' hβ'',
  obtain ⟨γ, hγ, Hγ, Hγ'⟩ := qam_A_is_sa_iff_aux8 α β Hβ,
  have Hβ' := qam_A_is_sa_iff_aux9 x α β γ hγ Hγ' hβ,
  exact ⟨Hβ', qam_A_is_sa_iff_aux5_aux6 x' this h Hβ'⟩,
end

lemma qam_A.of_is_self_adjoint (x : {x : ℍ // x ≠ 0}) (h : (qam_A hφ.elim x).adjoint = qam_A hφ.elim x) :
  (x : ℍ).is_almost_hermitian ∧ commute φ.matrix (x : ℍ) :=
begin
  simp_rw [qam_A, linear_map.adjoint_smul, linear_map.mul_eq_comp, linear_map.adjoint_comp,
    linear_map.adjoint_adjoint, linear_map.matrix.mul_left_adjoint,
    ← linear_map.mul_eq_comp, ← (linear_map.commute_mul_left_right _ _).eq,
    conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq] at h,
  have : linear_map.mul_right ℂ (φ.matrix ⬝ (x : ℍ))
    = ((linear_map.mul_right ℂ (φ.matrix ⬝ (x : ℍ)ᴴ)).adjoint),
  { simp_rw [linear_map.matrix.mul_right_adjoint, conj_transpose_mul,
      conj_transpose_conj_transpose, hφ.elim.matrix_is_pos_def.1.eq, sig_apply_matrix_mul_pos_def'], },
  nth_rewrite_lhs 0 this at h,
  simp_rw [← rank_one_Psi_transpose_to_lin, ← one_map_transpose_eq,
    ← smul_hom_class.map_smul] at h,
  simp only [(alg_equiv.injective _).eq_iff, (linear_equiv.injective _).eq_iff,
    (star_alg_equiv.injective _).eq_iff] at h,
  have : 1 / ((‖(x : ℍ)‖ : ℂ) ^ 2) ≠ 0,
  { simp_rw [ne.def, div_eq_zero_iff, one_ne_zero, false_or, sq_eq_zero_iff,
      complex.of_real_eq_zero, norm_eq_zero],
    exact subtype.mem x, },
  letI gg : no_zero_smul_divisors ℂ l(ℍ) := linear_map.no_zero_smul_divisors,
  simp_rw [star_ring_end_apply, star_div', star_one, complex.star_def, ← complex.of_real_pow,
    complex.conj_of_real, complex.of_real_pow, @smul_right_inj ℂ _ _ _ _ gg _ this] at h,
  rw [qam_A_is_sa_iff_aux, qam_A_is_sa_iff_aux2] at h,
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [← linear_map.comp_assoc, linear_map.mul_left_comp_inj] at h,
  have h' := qam_A_is_sa_iff_aux5 x h,
  exact qam_A_is_sa_iff_aux6 x h',
end

lemma qam_A.is_self_adjoint_of (x : {x : ℍ // x ≠ 0})
  (hx₁ : is_almost_hermitian (x : ℍ))
  (hx₂ : commute φ.matrix x) :
  (qam_A hφ.elim x).adjoint = qam_A hφ.elim x :=
begin
  simp_rw [qam_A, linear_map.adjoint_smul, linear_map.mul_eq_comp, linear_map.adjoint_comp,
    linear_map.adjoint_adjoint, linear_map.matrix.mul_left_adjoint, ← linear_map.mul_eq_comp,
    ← (linear_map.commute_mul_left_right _ _).eq, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq],
  obtain ⟨α, y, ⟨hxy, hy⟩⟩ := hx₁,
  have : 1 / ((‖(x : ℍ)‖ : ℂ) ^ 2) ≠ 0,
  { simp_rw [ne.def, div_eq_zero_iff, one_ne_zero, false_or, sq_eq_zero_iff,
      complex.of_real_eq_zero, norm_eq_zero],
    exact subtype.mem x, },
  letI gg : no_zero_smul_divisors ℂ l(ℍ) := linear_map.no_zero_smul_divisors,
  simp_rw [star_ring_end_apply, star_div', star_one, complex.star_def, ← complex.of_real_pow,
    complex.conj_of_real, complex.of_real_pow, @smul_right_inj ℂ _ _ _ _ gg _ this],
  simp_rw [← mul_eq_mul, ← hx₂.eq, ← hxy, conj_transpose_smul, mul_smul_comm,
    linear_map.mul_left_smul, linear_map.mul_right_smul, linear_map.adjoint_smul,
    smul_mul_smul, star_ring_end_apply, mul_comm, linear_map.matrix.mul_right_adjoint,
    mul_eq_mul, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq, hy.eq,
    sig_apply_matrix_mul_pos_def'],
end

lemma qam_A.is_self_adjoint_iff (x : {x : ℍ // x ≠ 0}) :
  (qam_A hφ.elim x).adjoint = qam_A hφ.elim x ↔ is_almost_hermitian (x : ℍ) ∧ commute φ.matrix x :=
⟨λ h, qam_A.of_is_self_adjoint x h, λ h, qam_A.is_self_adjoint_of x h.1 h.2⟩

lemma qam_A.is_real_qam (x : {x : ℍ // x ≠ 0}) :
  real_qam hφ.elim (qam_A hφ.elim x) :=
⟨qam_A.is_idempotent _, qam_A.is_real _⟩

lemma matrix.pos_def.ne_zero [nontrivial n] {Q : ℍ} (hQ : Q.pos_def) :
  Q ≠ 0 :=
begin
  have := pos_def.trace_ne_zero hQ,
  intros h,
  rw [h, trace_zero] at this,
  contradiction,
end

lemma qam_A.edges (x : {x : ℍ // x ≠ 0}) :
  (@qam_A.is_real_qam n _ _ φ hφ x).edges = 1 :=
begin
  rw real_qam.edges_eq_one_iff,
  exact ⟨x, rfl⟩,
end

lemma qam_A.is_irreflexive_iff [nontrivial n] (x : {x : ℍ // x ≠ 0}) :
  qam.refl_idempotent hφ.elim (qam_A hφ.elim x) 1 = 0 ↔ (x : ℍ).trace = 0 :=
begin
  simp_rw [qam_A, ← rank_one_to_matrix_transpose_Psi_symm,
    ← function.injective.eq_iff (hφ.elim.Psi 0 (1/2)).injective,
    Psi.refl_idempotent, smul_hom_class.map_smul, linear_equiv.apply_symm_apply,
    Psi.one, smul_mul_assoc, ← one_map_transpose_symm_eq, ← _root_.map_mul,
    map_zero, smul_eq_zero, star_alg_equiv.map_eq_zero_iff, alg_equiv.map_eq_zero_iff,
    ← rank_one_lm_eq_rank_one, one_div, inv_eq_zero, sq_eq_zero_iff, complex.of_real_eq_zero,
    norm_eq_zero, set.mem_set_of.mp (subtype.mem x), false_or, linear_map.mul_eq_comp,
    rank_one_lm_comp_rank_one_lm, smul_eq_zero, rank_one_lm_eq_rank_one,
    continuous_linear_map.coe_eq_zero, rank_one.eq_zero_iff,
    matrix.pos_def.ne_zero hφ.elim.matrix_is_pos_def.inv, or_false,
    set.mem_set_of.mp (subtype.mem x), or_false, linear_map.is_faithful_pos_map.inner_eq'],
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  rw [trace_mul_cycle, matrix.mul_assoc, inv_mul_cancel_left_of_invertible,
    ← trace_star, star_eq_zero],
  simp only [iff_self],
end

lemma qam_A.is_almost_injective (x y : {x : ℍ // x ≠ 0}) :
  qam_A hφ.elim x = qam_A hφ.elim y ↔ ∃ α : ℂˣ, (x : ℍ) = (α : ℂ) • (y : ℍ) :=
begin
  simp_rw [qam_A, ← rank_one_to_matrix_transpose_Psi_symm,
    ← smul_hom_class.map_smul, ← one_map_transpose_symm_eq],
  rw [function.injective.eq_iff ((hφ.elim.Psi _ _).symm).injective,
    function.injective.eq_iff (one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    function.injective.eq_iff hφ.elim.to_matrix.injective],
  have : ∀ x : {x : ℍ // x ≠ 0}, (1 / (‖(x : ℍ)‖ : ℂ) ^ 2) • (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ))
    = |(1 / (‖(x : ℍ)‖ : ℂ)) • (x : ℍ)⟩⟨(1 / (‖(x : ℍ)‖ : ℂ)) • (x : ℍ)|,
  { intros y,
    simp_rw [← rank_one_lm_eq_rank_one, rank_one_lm_smul, smul_rank_one_lm,
      smul_smul, star_ring_end_apply, star_div', star_one, complex.star_def,
      complex.conj_of_real, ← div_mul_eq_div_mul_one_div, ← sq], },
  simp_rw [this, continuous_linear_map.coe_inj],
  split,
  { intro h,
    obtain ⟨α, hα⟩ := rank_one.ext_iff _ _ h,
    let β := (‖(x : ℍ)‖ : ℂ) * (α : ℂ) * (1 / (‖(y : ℍ)‖ : ℂ)),
    have : β ≠ 0,
    { simp_rw [β, one_div],
      apply mul_ne_zero,
      apply mul_ne_zero,
      work_on_goal 2
      { exact units.ne_zero _, },
      work_on_goal 2
      { apply inv_ne_zero, },
      all_goals
      { simp only [complex.of_real_ne_zero, norm_ne_zero_iff],
        simp only [ne.def, set.mem_set_of.mp (subtype.mem x), set.mem_set_of.mp (subtype.mem y),
        not_false_iff], }, },
    use units.mk0 β this,
    simp_rw [units.coe_mk0, β, mul_assoc],
    rw [← smul_smul],
    rw smul_smul at hα,
    rw [← hα, smul_smul, one_div, ← complex.of_real_inv, ← complex.of_real_mul,
      mul_inv_cancel (norm_ne_zero_iff.mpr (set.mem_set_of.mp (subtype.mem x))),
      complex.of_real_one, one_smul], },
  { rintros ⟨α, hα⟩,
    simp_rw [← continuous_linear_map.coe_inj, ← this, hα, ← rank_one_lm_eq_rank_one,
      rank_one_lm_smul, smul_rank_one_lm, smul_smul, norm_smul,
      ← complex.norm_sq_eq_conj_mul_self, complex.norm_sq_eq_abs, ← complex.norm_eq_abs],
    simp only [complex.of_real_mul, one_div, mul_pow, _root_.mul_inv_rev, mul_assoc],
    rw [complex.of_real_pow, inv_mul_cancel, mul_one],
    { simp only [ne.def, sq_eq_zero_iff, complex.of_real_eq_zero, norm_eq_zero],
      exact units.ne_zero _, }, },
end

lemma qam_A.is_reflexive_iff [nontrivial n] (x : {x : ℍ // x ≠ 0}) :
  qam.refl_idempotent hφ.elim (qam_A hφ.elim x) 1 = 1 ↔ ∃ α : ℂˣ, (x : ℍ) = (α : ℂ) • φ.matrix⁻¹ :=
begin
  simp_rw [qam_A, ← rank_one_to_matrix_transpose_Psi_symm,
    ← function.injective.eq_iff (hφ.elim.Psi 0 (1/2)).injective,
    Psi.refl_idempotent, smul_hom_class.map_smul, linear_equiv.apply_symm_apply,
    Psi.one, smul_mul_assoc, ← one_map_transpose_symm_eq, ← _root_.map_mul,
    ← smul_hom_class.map_smul],
  rw [function.injective.eq_iff (one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    function.injective.eq_iff (hφ.elim.to_matrix).injective],
  simp_rw [← rank_one_lm_eq_rank_one, linear_map.mul_eq_comp, rank_one_lm_comp_rank_one_lm,
    ← smul_rank_one_lm, rank_one_lm_eq_rank_one, continuous_linear_map.coe_inj],
  rw [← sub_eq_zero, ← rank_one.left_sub, rank_one.eq_zero_iff],
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  simp only [sub_eq_zero, smul_smul, linear_map.is_faithful_pos_map.inner_eq'],
  rw [trace_mul_cycle, inv_mul_of_invertible, matrix.one_mul, ← trace_star],
  simp only [hφ.elim.matrix_is_pos_def.inv.ne_zero, or_false],
  split,
  { intros h,
    simp_rw [← h, smul_smul],
    have : (x : ℍ).trace ≠ 0,
    { intro h',
      rw [h', star_zero, mul_zero, zero_smul] at h,
      exact hφ.elim.matrix_is_pos_def.inv.ne_zero h.symm, },
    have : 1 / ↑‖(x : ℍ)‖ ^ 2 * star (x : ℍ).trace ≠ 0,
    { apply mul_ne_zero,
      { simp only [one_div, inv_eq_zero, ne.def, sq_eq_zero_iff, complex.of_real_eq_zero,
          norm_eq_zero],
        exact subtype.mem x, },
      { simp only [ne.def, star_eq_zero],
        exact this, }, },
    use units.mk0 _ (inv_ne_zero this),
    rw [units.coe_mk0, inv_mul_cancel this, one_smul], },
  { rintros ⟨α, hx⟩,
    simp_rw [hx, trace_smul, star_smul, norm_smul, trace_star, hφ.elim.matrix_is_pos_def.inv.1.eq],
    have : (‖φ.matrix⁻¹‖ : ℂ) ^ 2 = (φ.matrix⁻¹).trace,
    { simp_rw [← inner_self_eq_norm_sq_to_K, linear_map.is_faithful_pos_map.inner_eq',
        hφ.elim.matrix_is_pos_def.inv.1.eq, matrix.mul_assoc, mul_inv_cancel_left_of_invertible], },
    simp only [complex.of_real_mul, mul_pow, one_div, _root_.mul_inv_rev,
      this, smul_smul, smul_eq_mul],
    rw [mul_rotate, mul_rotate _ _ (α : ℂ), mul_assoc _ _ (star (α : ℂ)),
      complex.star_def, complex.mul_conj, mul_mul_mul_comm, complex.norm_sq_eq_abs,
      ← complex.norm_eq_abs, ← complex.of_real_pow, ← complex.of_real_inv, ← complex.of_real_mul,
      mul_inv_cancel (pos_def.trace_ne_zero hφ.elim.matrix_is_pos_def.inv), mul_inv_cancel,
      one_mul, complex.of_real_one, one_smul],
    simp only [ne.def, sq_eq_zero_iff, norm_eq_zero, units.ne_zero, not_false_iff], },
end

lemma qam_A.of_trivial_graph [nontrivial n] :
  qam_A hφ.elim ⟨φ.matrix⁻¹, hφ.elim.matrix_is_pos_def.inv.ne_zero⟩ = qam.trivial_graph hφ.elim :=
begin
  rw qam_A,
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  simp only [linear_map.mul_left_smul, linear_map.mul_right_smul, linear_map.adjoint_smul,
    subtype.coe_mk, inv_mul_of_invertible, mul_inv_of_invertible, linear_map.mul_left_one,
    linear_map.mul_right_one, ← linear_map.one_eq_id, linear_map.adjoint_one, one_mul],
  have : ((‖φ.matrix⁻¹‖ : ℝ) : ℂ) ^ 2 = (φ.matrix⁻¹).trace,
  { simp_rw [← inner_self_eq_norm_sq_to_K, linear_map.is_faithful_pos_map.inner_eq',
      hφ.elim.matrix_is_pos_def.inv.1.eq, matrix.mul_assoc, mul_inv_cancel_left_of_invertible], },
  rw [this, one_div, qam.trivial_graph_eq],
end

lemma qam.unique_one_edge_and_refl [nontrivial n] {A : l(ℍ)}
  (hA : real_qam hφ.elim A) :
  (hA.edges = 1 ∧ qam.refl_idempotent hφ.elim A 1 = 1)
    ↔ A = qam.trivial_graph hφ.elim :=
begin
  split,
  { rintros ⟨h1, h2⟩,
    rw real_qam.edges_eq_one_iff at h1,
    rcases h1 with ⟨x, rfl⟩,
    rw ← qam_A_eq at h2,
    rw [← qam_A_eq, ← qam_A.of_trivial_graph, qam_A.is_almost_injective],
    exact (qam_A.is_reflexive_iff x).mp h2, },
  { rintros rfl,
    exact ⟨qam.trivial_graph_edges, qam.nontracial.trivial_graph⟩, },
end

private lemma star_alg_equiv.is_isometry_iff [nontrivial n] (f : ℍ ≃⋆ₐ[ℂ] ℍ) :
  @star_alg_equiv.is_isometry n _ _ φ hφ f ↔ f φ.matrix = φ.matrix :=
begin
  simp_rw [list.tfae.out (@linear_map.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 0 4, star_alg_equiv.is_isometry,
    iff_self],
end

lemma qam_A.isometric_star_alg_equiv_conj [nontrivial n] (x : {x : ℍ // x ≠ 0}) {f : ℍ ≃⋆ₐ[ℂ] ℍ}
  (hf : @star_alg_equiv.is_isometry n _ _ φ hφ f) :
  f.to_alg_equiv.to_linear_map ∘ₗ qam_A hφ.elim x ∘ₗ f.symm.to_alg_equiv.to_linear_map
    = qam_A hφ.elim (⟨f (x : ℍ), (linear_equiv.map_ne_zero_iff f.to_alg_equiv.to_linear_equiv).mpr
      (set.mem_set_of.mp (subtype.mem x))⟩) :=
begin
  apply_fun (hφ.elim.to_matrix) using alg_equiv.injective,
  have hf' := hf,
  rw star_alg_equiv.is_isometry_iff at hf,
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  have this2 : f φ.matrix⁻¹ = φ.matrix⁻¹,
  { symmetry,
    apply inv_eq_left_inv,
    nth_rewrite 1 ← hf,
    rw [← mul_eq_mul, ← _root_.map_mul, mul_eq_mul, inv_mul_of_invertible, _root_.map_one], },
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner,
  have hU : commute φ.matrix (U⁻¹ : unitary_group n ℂ),
  { rw [← inner_aut_adjoint_eq_iff, ← inner_aut_star_alg_equiv_to_linear_map,
      ← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map],
    rw [eq_comm, ← star_alg_equiv.symm_apply_eq,
      (list.tfae.out (@linear_map.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ (inner_aut_star_alg U).symm) 0 1),
      star_alg_equiv.symm_symm, inner_aut_star_alg_equiv_symm_to_linear_map,
      inner_aut_star_alg_equiv_to_linear_map] at hf,
    rw [inner_aut_star_alg_equiv_to_linear_map, inner_aut_star_alg_equiv_symm_to_linear_map,
      inv_inv, hf], },
  simp only [← linear_map.mul_eq_comp, alg_equiv.map_mul, inner_aut_star_alg_equiv_to_linear_map,
    inner_aut_star_alg_equiv_symm_to_linear_map, inner_aut.to_matrix, qam_A.to_matrix,
    mul_eq_mul, matrix.smul_mul, matrix.mul_smul, ← mul_kronecker_mul, ← matrix.conj_mul],
  let σ := hφ.elim.sig,
  let rpow := hφ.elim.matrix_is_pos_def.rpow,
  have := calc σ (-(1 / 2)) U ⬝ (rpow (1 / 2) ⬝ (x : ℍ) ⬝ rpow (1 / 2) ⬝ (σ (-(1 / 2)))
    (U⁻¹ : unitary_group n ℂ))
    = rpow (1/2) ⬝ U ⬝ (rpow (-(1/2)) ⬝ rpow (1/2)) ⬝ (x : ℍ) ⬝ (rpow (1/2) ⬝ rpow (1/2))
      ⬝ (U⁻¹ : unitary_group n ℂ) ⬝ rpow (-(1/2)) :
  by { simp only [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc, σ, rpow, neg_neg], }
  ... = rpow (1/2) ⬝ U ⬝ (x : ℍ) ⬝ (φ.matrix ⬝ (U⁻¹ : unitary_group n ℂ)) ⬝ rpow (-(1/2)) :
  by { simp only [pos_def.rpow_mul_rpow, neg_add_self, pos_def.rpow_zero, matrix.mul_one,
    add_halves, pos_def.rpow_one_eq_self, matrix.mul_assoc], }
  ... = rpow (1/2) ⬝ U ⬝ (x : ℍ) ⬝ (U⁻¹ : unitary_group n ℂ) ⬝ (rpow 1 ⬝ rpow (-(1/2))) :
  by { simp_rw [← mul_eq_mul, hU.eq, rpow, pos_def.rpow_one_eq_self, mul_assoc], }
  ... = rpow (1/2) ⬝ U ⬝ (x : ℍ) ⬝ (U⁻¹ : unitary_group n ℂ) ⬝ rpow (1/2) :
  by { simp only [rpow, pos_def.rpow_mul_rpow],
    norm_num, },
  simp only [this, subtype.coe_mk],
  rw star_alg_equiv.is_isometry at hf',
  simp_rw [hf', inner_aut_star_alg_apply, matrix.mul_assoc, ← mul_eq_mul, hU.eq,
    unitary_group.inv_apply],
  refl,
end

lemma qam_A.iso_iff [nontrivial n] {x y : {x : ℍ // x ≠ 0}}
  -- (hx : _root_.is_self_adjoint (qam_A hφ.elim x))
  -- (hy : _root_.is_self_adjoint (qam_A hφ.elim y))
  :
  qam.iso (@qam_A.is_idempotent n _ _ φ hφ x) (qam_A.is_idempotent y)
    ↔ ∃ U : unitary_group n ℂ, (∃ β : ℂˣ, (x : ℍ) = inner_aut U ((β : ℂ) • (y : ℍ)))
      ∧ commute φ.matrix U :=
begin
  simp_rw [qam.iso_iff, ← inner_aut_star_alg_equiv_to_linear_map, star_alg_equiv.comp_eq_iff],
  split,
  { rintros ⟨U, ⟨hU, hUU⟩⟩,
    refine ⟨U, _, hUU⟩,
    rw [unitary_commutes_with_hφ_matrix_iff_is_isometry] at hUU,
    rw [linear_map.comp_assoc, qam_A.isometric_star_alg_equiv_conj _ hUU,
      qam_A.is_almost_injective, subtype.coe_mk] at hU,
    simp_rw [smul_hom_class.map_smul, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv],
    exact hU, },
  { rintros ⟨U, ⟨hU, hUU⟩⟩,
    refine ⟨U, _, hUU⟩,
    rw unitary_commutes_with_hφ_matrix_iff_is_isometry at hUU,
    rw [linear_map.comp_assoc, qam_A.isometric_star_alg_equiv_conj _ hUU,
      qam_A.is_almost_injective, subtype.coe_mk],
    simp_rw [smul_hom_class.map_smul, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv] at hU,
    exact hU, },
end
