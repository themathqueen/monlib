/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.nontracial
import linear_algebra.my_ips.minimal_proj
import quantum_graph.iso

/-!

# Quantum graphs as projections

This file contains the definition of a quantum graph as a projection, and the proof that the 

-/

variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]

open_locale tensor_product big_operators kronecker functional

local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

variables {φ : ℍ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map]
  {ψ : matrix p p ℂ →ₗ[ℂ] ℂ} (hψ : ψ.is_faithful_pos_map)

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

lemma rank_one_Psi_transpose_to_lin (x y : ℍ) :
  hφ.elim.to_matrix.symm ((tensor_product.map id (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
    ((hφ.elim.Psi 0 (1/2)) (|x⟩⟨y|))).to_kronecker
  = (linear_map.mul_left ℂ x) *  ((linear_map.mul_right ℂ y).adjoint : l(ℍ)) :=
begin
  let b := @linear_map.is_faithful_pos_map.orthonormal_basis n _ _ φ _,
  rw ← function.injective.eq_iff hφ.elim.to_matrix.injective,
  simp_rw [_root_.map_mul, linear_map.matrix.mul_right_adjoint, linear_map.mul_right_to_matrix,
    linear_map.mul_left_to_matrix, matrix.mul_eq_mul, ← mul_kronecker_mul, matrix.one_mul,
    matrix.mul_one, linear_map.is_faithful_pos_map.sig_apply_sig],
  have : (1 / 2 : ℝ) + -1 = - (1 / 2) := by norm_num,
  rw [this, ← linear_map.is_faithful_pos_map.sig_conj_transpose, alg_equiv.apply_symm_apply,
    linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply, tensor_product.map_tmul,
    tensor_product.to_kronecker_apply, linear_map.is_faithful_pos_map.sig_zero,
    linear_map.one_apply, alg_equiv.to_linear_map_apply, op, linear_equiv.coe_coe,
    mul_opposite.coe_op_linear_equiv, transpose_alg_equiv_symm_op_apply],
end

private lemma matrix.std_basis_matrix.transpose' {R n p : Type*} [decidable_eq n] [decidable_eq p]
  [semiring R] (i : n) (j : p) :
  (std_basis_matrix i j (1 : R))ᵀ = std_basis_matrix j i (1 : R) :=
begin
  ext1,
  simp_rw [transpose_apply, std_basis_matrix, and_comm],
end

lemma rank_one_to_matrix_transpose_Psi_symm (x y : ℍ) :
  (hφ.elim.Psi 0 (1/2)).symm ((tensor_product.map id (transpose_alg_equiv n ℂ ℂ).to_linear_map)
      (hφ.elim.to_matrix (|x⟩⟨y|)).kronecker_to_tensor_product)
  = (linear_map.mul_left ℂ (x ⬝ φ.matrix))
    * ((linear_map.mul_right ℂ (φ.matrix ⬝ y)).adjoint : l(ℍ)) :=
begin
  rw kmul_representation (hφ.elim.to_matrix (|x⟩⟨y|)),
  simp_rw [map_sum, smul_hom_class.map_smul, kronecker_to_tensor_product_apply,
    tensor_product.map_tmul, linear_map.one_apply, alg_equiv.to_linear_map_apply,
    transpose_alg_equiv_apply, linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_symm_mk,
    linear_map.is_faithful_pos_map.Psi_inv_fun'_apply, unop, linear_equiv.coe_coe,
    mul_opposite.coe_op_linear_equiv_symm, mul_opposite.unop_op,
    matrix.std_basis_matrix.transpose', std_basis_matrix_conj_transpose,
    neg_zero, linear_map.is_faithful_pos_map.sig_zero, star_one,
    linear_map.matrix.mul_right_adjoint, linear_map.ext_iff, linear_map.sum_apply,
    linear_map.mul_apply, linear_map.smul_apply, continuous_linear_map.coe_coe,
    rank_one_apply, rank_one_to_matrix, conj_transpose_col, ← vec_mul_vec_eq,
    vec_mul_vec_apply, pi.star_apply, linear_map.mul_left_apply, linear_map.mul_right_apply,
    reshape_apply],
  have : ∀ (i j : n) (a : ℍ), ⟪hφ.elim.sig (-(1/2)) e_{i,j}, a⟫_ℂ
    = ⟪e_{i,j} ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)), hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ a⟫_ℂ,
  { intros i j a,
    simp_rw [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc, neg_neg,
      ← linear_map.is_faithful_pos_map.basis_apply hφ.elim (i,j),
      linear_map.is_faithful_pos_map.inner_left_mul,
      linear_map.is_faithful_pos_map.inner_coord', (pos_def.rpow.is_hermitian _ _).eq], },
  intros a,
  simp_rw [this, ← hφ.elim.basis_apply (_,_), linear_map.is_faithful_pos_map.inner_coord',
    ← conj_transpose_apply, smul_smul, mul_assoc, ← finset.sum_smul, ← finset.mul_sum,
    mul_comm _ ((_ ⬝ a ⬝ _) _ _), ← mul_apply, ← smul_std_basis_matrix', conj_transpose_mul,
    (pos_def.rpow.is_hermitian _ _).eq, matrix.mul_assoc, ← matrix.mul_assoc
      (hφ.elim.matrix_is_pos_def.rpow _) (hφ.elim.matrix_is_pos_def.rpow _),
    pos_def.rpow_mul_rpow, add_halves, pos_def.rpow_one_eq_self,
    hφ.elim.matrix_is_pos_def.1.eq, sig_apply_matrix_mul_pos_def', ← mul_eq_mul,
    ← mul_assoc],
  nth_rewrite_lhs 0 [← matrix_eq_sum_std_basis],
end

@[instance] private def hmm {H : Type*} [normed_add_comm_group H]
  [inner_product_space ℂ H] [finite_dimensional ℂ H] (U : submodule ℂ H) :
  complete_space U :=
finite_dimensional.complete ℂ U

private lemma lm_to_clm_comp {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] {p q : E →ₗ[𝕜] E} :
  p.to_continuous_linear_map * q.to_continuous_linear_map
    = (p * q).to_continuous_linear_map :=
rfl

private lemma is_idempotent_elem_to_clm {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
  is_idempotent_elem p ↔ is_idempotent_elem p.to_continuous_linear_map :=
begin
  simp_rw [is_idempotent_elem, lm_to_clm_comp,
    function.injective.eq_iff (linear_equiv.injective _), iff_self],
end

private lemma is_self_adjoint_to_clm {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E]
  [finite_dimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
  is_self_adjoint p ↔ is_self_adjoint p.to_continuous_linear_map :=
begin
  simp_rw [_root_.is_self_adjoint, continuous_linear_map.star_eq_adjoint,
    ← linear_map.adjoint_to_continuous_linear_map,
    function.injective.eq_iff (linear_equiv.injective _), linear_map.star_eq_adjoint,
    iff_self],
end

lemma orthogonal_projection_iff_lm {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E]
  [finite_dimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
(∃ (U : submodule 𝕜 E), (orthogonal_projection' U : E →ₗ[𝕜] E) = p)
  ↔ is_self_adjoint p ∧ is_idempotent_elem p :=
begin
  have := @orthogonal_projection_iff 𝕜 E _ _ _ _ _ p.to_continuous_linear_map,
  simp_rw [is_idempotent_elem_to_clm, is_self_adjoint_to_clm] at ⊢ this,
  rw [← this],
  split,
  all_goals { rintros ⟨U, hU⟩,
    use U },
  { rw [← hU],
    refl },
  { rw hU,
    refl, },
end

noncomputable def one_map_transpose :
  (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] (matrix (n × n) (n × n) ℂ) :=
begin
  apply star_alg_equiv.of_alg_equiv _ _,
  { apply alg_equiv.of_linear_equiv _ _ _,
    { apply linear_equiv.of_linear
        (tensor_product.to_kronecker.comp (tensor_product.map (1 : ℍ →ₗ[ℂ] ℍ)
          (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map))
        ((tensor_product.map (1 : ℍ →ₗ[ℂ] ℍ)
          (transpose_alg_equiv n ℂ ℂ).to_linear_map).comp kronecker_to_tensor_product),
      work_on_goal 1 { rw kronecker_product.ext_iff, },
      work_on_goal 2 { rw tensor_product.ext_iff, },
      all_goals { intros x y,
        simp only [linear_map.comp_apply, kronecker_to_tensor_product_apply, tensor_product.map_tmul,
          tensor_product.to_kronecker_apply, alg_equiv.to_linear_map_apply, alg_equiv.symm_apply_apply,
          alg_equiv.apply_symm_apply, linear_map.one_apply, linear_map.id_apply], }, },
    { intros x y,
      simp_rw [linear_equiv.of_linear_apply],
      apply x.induction_on,
      { simp only [zero_mul, map_zero], },
      { intros x₁ x₂,
        apply y.induction_on,
        { simp only [mul_zero, map_zero], },
        { intros y₁ y₂,
          simp only [tensor_product.map_tmul, linear_map.comp_apply,
            algebra.tensor_product.tmul_mul_tmul, tensor_product.to_kronecker_apply,
            linear_map.one_apply, mul_eq_mul, ← mul_kronecker_mul, alg_equiv.to_linear_map_apply,
            _root_.map_mul], },
        { simp only [mul_add, map_add],
          intros z w hz hw,
          simp_rw [hz, hw], }, },
      { simp only [add_mul, map_add],
        intros z w hz hw,
        simp_rw [hz, hw], }, },
    { intros r,
      simp_rw [linear_equiv.of_linear_apply, algebra.algebra_map_eq_smul_one,
        smul_hom_class.map_smul, algebra.tensor_product.one_def, linear_map.comp_apply,
        tensor_product.map_tmul, tensor_product.to_kronecker_apply, alg_equiv.to_linear_map_apply,
        _root_.map_one, linear_map.one_apply, one_kronecker_one], }, },
  { intros,
    simp only [alg_equiv.of_linear_equiv_apply, linear_equiv.of_linear_apply],
    apply x.induction_on,
    { simp only [mul_zero, map_zero, tensor_product.star_tmul, star_zero, conj_transpose_zero], },
    { intros y₁ y₂,
      simp only [tensor_product.map_tmul, linear_map.comp_apply,
        algebra.tensor_product.tmul_mul_tmul, tensor_product.to_kronecker_apply,
        linear_map.one_apply, mul_eq_mul, ← mul_kronecker_mul, alg_equiv.to_linear_map_apply,
        _root_.map_mul, star_eq_conj_transpose, kronecker_conj_transpose,
        tensor_op_star_apply, op, linear_equiv.coe_coe, mul_opposite.coe_op_linear_equiv,
        transpose_alg_equiv_symm_op_apply],
      let y' := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) y₂,
      have : y₂ = mul_opposite.op y' := rfl,
      simp only [this, transpose_alg_equiv_symm_op_apply, unop, linear_equiv.coe_coe,
        mul_opposite.coe_op_linear_equiv_symm, mul_opposite.unop_op],
      have : (y'ᴴ)ᵀ = y'ᵀᴴ := by ext1; simp only [transpose_apply, conj_transpose_apply],
      simp_rw [this], },
    { simp only [mul_add, map_add, conj_transpose_add, star_add],
      intros z w hz hw,
      simp_rw [hz, hw], }, },
end

lemma one_map_transpose_eq (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
  (one_map_transpose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _) x = ((tensor_product.map (1 : l(ℍ))
    (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map) x).to_kronecker :=
rfl
lemma one_map_transpose_symm_eq (x : ⊗K) :
  (one_map_transpose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _).symm x = ((tensor_product.map (1 : l(ℍ))
    (transpose_alg_equiv n ℂ ℂ).to_linear_map) x.kronecker_to_tensor_product) :=
rfl

lemma one_map_transpose_apply (x y : ℍ) :
  (one_map_transpose : _ ≃⋆ₐ[ℂ] ⊗K) (x ⊗ₜ mul_opposite.op y) = x ⊗ₖ yᵀ :=
begin
  rw [one_map_transpose_eq, tensor_product.map_tmul, alg_equiv.to_linear_map_apply,
    tensor_product.to_kronecker_apply, transpose_alg_equiv_symm_op_apply],
  refl,
end

lemma to_matrix''_map_star (x : l(ℍ)) :
  (hφ.elim.to_matrix (x : l(ℍ)).adjoint) =
    star (hφ.elim.to_matrix x) :=
begin
  ext1,
  simp only [linear_map.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    pi.star_apply, star_apply, star_eq_conj_transpose, conj_transpose_apply,
    linear_map.star_eq_adjoint, linear_map.adjoint_inner_right, is_R_or_C.star_def,
    inner_conj_symm, linear_map.is_faithful_pos_map.basis_repr_apply],
end
private lemma ffsugh {x : matrix (n × n) (n × n) ℂ} {y : l(ℍ)} :
  hφ.elim.to_matrix.symm x = y ↔ x = hφ.elim.to_matrix y :=
equiv.symm_apply_eq _
lemma to_matrix''_symm_map_star (x : ⊗K) :
  hφ.elim.to_matrix.symm (star x) = ((hφ.elim.to_matrix.symm x).adjoint) :=
begin
  rw [ffsugh, to_matrix''_map_star, alg_equiv.apply_symm_apply],
end

lemma qam.idempotent_and_real_iff_exists_ortho_proj (A : l(ℍ)) :
  (qam.refl_idempotent hφ.elim A A = A ∧ A.is_real) ↔
    ∃ (U : submodule ℂ ℍ),
      (orthogonal_projection' U : l(ℍ))
      = (hφ.elim.to_matrix.symm ((tensor_product.map id (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
      ((hφ.elim.Psi 0 (1/2)) A)).to_kronecker) :=
begin
  rw [qam.is_real_and_idempotent_iff_Psi_orthogonal_projection,
    orthogonal_projection_iff_lm, ← one_map_transpose_eq, is_idempotent_elem.alg_equiv,
    is_idempotent_elem.star_alg_equiv, and_comm],
  simp_rw [_root_.is_self_adjoint, linear_map.star_eq_adjoint, ← to_matrix''_symm_map_star,
    ← map_star, function.injective.eq_iff (alg_equiv.injective _),
    function.injective.eq_iff (star_alg_equiv.injective _), iff_self],
end

noncomputable def qam.submodule_of_idempotent_and_real {A : l(ℍ)}
  (hA1 : qam.refl_idempotent hφ.elim A A = A) (hA2 : A.is_real) :
  submodule ℂ ℍ :=
begin
  choose U hU using (qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩,
  exact U,
end

lemma qam.orthogonal_projection'_eq {A : l(ℍ)} (hA1 : qam.refl_idempotent hφ.elim A A = A)
  (hA2 : A.is_real) :
  (orthogonal_projection' (qam.submodule_of_idempotent_and_real hA1 hA2) : l(ℍ))
  = (hφ.elim.to_matrix.symm ((tensor_product.map id (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
    ((hφ.elim.Psi 0 (1/2)) A)).to_kronecker) :=
(qam.submodule_of_idempotent_and_real._proof_8 hA1 hA2)

noncomputable def qam.onb_of_idempotent_and_real {A : l(ℍ)}
  (hA1 : qam.refl_idempotent hφ.elim A A = A) (hA2 : A.is_real) :
  orthonormal_basis
    (fin (finite_dimensional.finrank ℂ (qam.submodule_of_idempotent_and_real hA1 hA2)))
    ℂ (qam.submodule_of_idempotent_and_real hA1 hA2) :=
std_orthonormal_basis ℂ _

lemma qam.idempotent_and_real.eq {A : l(ℍ)}
  (hA1 : qam.refl_idempotent hφ.elim A A = A) (hA2 : A.is_real) :
  A = ∑ i, linear_map.mul_left ℂ
    ((qam.onb_of_idempotent_and_real hA1 hA2 i : ℍ) ⬝ φ.matrix)
  * ((linear_map.mul_right ℂ
    (φ.matrix ⬝ (qam.onb_of_idempotent_and_real hA1 hA2 i : ℍ))).adjoint) :=
begin
  let U := qam.submodule_of_idempotent_and_real hA1 hA2,
  simp_rw [← rank_one_to_matrix_transpose_Psi_symm, ← map_sum, ← continuous_linear_map.coe_sum,
    ← orthonormal_basis.orthogonal_projection'_eq_sum_rank_one
      (qam.onb_of_idempotent_and_real hA1 hA2),
    qam.orthogonal_projection'_eq, alg_equiv.apply_symm_apply],
  simp_rw [← one_map_transpose_symm_eq, ← one_map_transpose_eq, star_alg_equiv.symm_apply_apply,
    linear_equiv.symm_apply_apply],
end

def real_qam (hφ : φ.is_faithful_pos_map) (A : l(ℍ)) :=
qam.refl_idempotent hφ A A = A ∧ A.is_real

lemma real_qam.add_iff {A B : ℍ →ₗ[ℂ] ℍ}
  (hA : real_qam hφ.elim A) (hB : real_qam hφ.elim B) :
  real_qam hφ.elim (A + B) ↔ qam.refl_idempotent hφ.elim A B + qam.refl_idempotent hφ.elim B A = 0 :=
begin
  simp only [real_qam] at ⊢ hA hB,
  simp_rw [map_add, linear_map.add_apply, hA, hB, add_assoc, add_left_cancel_iff,
    ← add_assoc, add_left_eq_self, add_comm, linear_map.is_real_iff, linear_map.real_add,
    (linear_map.is_real_iff _).mp hA.2, (linear_map.is_real_iff _).mp hB.2,
    eq_self_iff_true, and_true, iff_self],
end

def real_qam.zero :
  real_qam hφ.elim (0 : l(ℍ)) :=
begin
  simp_rw [real_qam, map_zero, eq_self_iff_true, true_and],
  intro,
  simp only [linear_map.zero_apply, star_zero],
end
@[instance] noncomputable def real_qam.has_zero :
  has_zero {x // real_qam hφ.elim x} :=
{ zero := ⟨0, real_qam.zero⟩ }
lemma qam.refl_idempotent_zero (a : l(ℍ)) :
  qam.refl_idempotent hφ.elim a 0 = 0 :=
map_zero _
lemma qam.zero_refl_idempotent (a : l(ℍ)) :
  qam.refl_idempotent hφ.elim 0 a = 0 :=
by simp_rw [map_zero, linear_map.zero_apply]

noncomputable def real_qam.edges {x : l(ℍ)} (hx : real_qam hφ.elim x) : ℕ :=
finite_dimensional.finrank ℂ (qam.submodule_of_idempotent_and_real hx.1 hx.2)

noncomputable def real_qam.edges' :
  {x : ℍ →ₗ[ℂ] ℍ // real_qam hφ.elim x} → ℕ :=
λ x, finite_dimensional.finrank ℂ
  (qam.submodule_of_idempotent_and_real
  (set.mem_set_of.mp (subtype.mem x)).1
  (set.mem_set_of.mp (subtype.mem x)).2)

lemma real_qam.edges_eq {A : l(ℍ)} (hA : real_qam hφ.elim A) :
  (hA.edges : ℂ) = (A φ.matrix⁻¹).trace :=
begin
  obtain ⟨hA1, hA2⟩ := hA,
  nth_rewrite_rhs 0 qam.idempotent_and_real.eq hA1 hA2,
  let U := qam.submodule_of_idempotent_and_real hA1 hA2,
  simp_rw [linear_map.sum_apply, linear_map.matrix.mul_right_adjoint, linear_map.mul_apply,
    linear_map.mul_right_apply, linear_map.mul_left_apply, conj_transpose_mul,
    hφ.elim.matrix_is_pos_def.1.eq, mul_eq_mul, ← matrix.mul_assoc, sig_apply_matrix_mul_pos_def'],
  have : ∀ x : fin (finite_dimensional.finrank ℂ ↥U),
    (((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ) ⬝ φ.matrix
      ⬝ (φ.matrix)⁻¹ ⬝ φ.matrix ⬝
      ((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ)ᴴ).trace
    = 1,
  { intros x,
    calc (((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ) ⬝ φ.matrix
      ⬝ (φ.matrix)⁻¹ ⬝ φ.matrix ⬝
      ((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ)ᴴ).trace
      = (((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ) ⬝ hφ.elim.matrix_is_pos_def.rpow 1
      ⬝ hφ.elim.matrix_is_pos_def.rpow (-1) ⬝ φ.matrix ⬝
      ((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ)ᴴ).trace :
    by { simp_rw [pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self], }
    ... = (((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ) ⬝ (hφ.elim.matrix_is_pos_def.rpow 1
      ⬝ hφ.elim.matrix_is_pos_def.rpow (-1)) ⬝ φ.matrix ⬝
      ((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ)ᴴ).trace :
    by { simp_rw [matrix.mul_assoc], }
    ... = (((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ) ⬝ φ.matrix ⬝
      ((qam.onb_of_idempotent_and_real hA1 hA2) x : ℍ)ᴴ).trace :
    by { simp_rw [pos_def.rpow_mul_rpow, add_neg_self, pos_def.rpow_zero, matrix.mul_one], }
    ... = ⟪↑(qam.onb_of_idempotent_and_real hA1 hA2 x),
      ↑(qam.onb_of_idempotent_and_real hA1 hA2 x)⟫_ℂ :
    by { simp_rw [linear_map.is_faithful_pos_map.inner_eq'],
      rw [← trace_mul_cycle], }
    ... = ⟪qam.onb_of_idempotent_and_real hA1 hA2 x,
      qam.onb_of_idempotent_and_real hA1 hA2 x⟫_ℂ : rfl
    ... = 1 : _,
    { rw [← orthonormal_basis.repr_apply_apply, orthonormal_basis.repr_self,
        euclidean_space.single_apply],
      simp_rw [eq_self_iff_true, if_true], }, },
  simp_rw [trace_sum, ← matrix.mul_assoc, this, finset.sum_const, finset.card_fin,
    nat.smul_one_eq_coe, nat.cast_inj],
  refl,
end

lemma complete_graph_real_qam :
  real_qam hφ.elim (qam.complete_graph hφ.elim) :=
⟨qam.nontracial.complete_graph.qam, qam.nontracial.complete_graph.is_real⟩

lemma qam.complete_graph_edges :
  (@complete_graph_real_qam n _ _ φ hφ).edges = finite_dimensional.finrank ℂ (⊤ : submodule ℂ ℍ) :=
begin
  have := calc
    (real_qam.edges complete_graph_real_qam : ℂ)
    = (qam.complete_graph hφ.elim φ.matrix⁻¹).trace : real_qam.edges_eq _,
  haveI ig := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [qam.complete_graph, continuous_linear_map.coe_coe,
    rank_one_apply, linear_map.is_faithful_pos_map.inner_eq',
    conj_transpose_one, matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one] at this,
  norm_cast at this,
  simp_rw [qam.complete_graph, this, finrank_top, finite_dimensional.finrank_matrix],
end

lemma qam.trivial_graph_real_qam [nontrivial n] :
  real_qam hφ.elim (qam.trivial_graph hφ.elim) :=
⟨qam.nontracial.trivial_graph.qam, qam.nontracial.trivial_graph.is_real⟩

lemma qam.trivial_graph_edges [nontrivial n] :
  (@qam.trivial_graph_real_qam n _ _ φ hφ _).edges = 1 :=
begin
  have := real_qam.edges_eq (@qam.trivial_graph_real_qam n _ _ φ _ _),
  haveI ig := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [qam.trivial_graph_eq, linear_map.smul_apply, linear_map.one_apply,
    trace_smul, smul_eq_mul, inv_mul_cancel (hφ.elim.matrix_is_pos_def.inv.trace_ne_zero)] at this,
  norm_cast at this,
  simp_rw [qam.trivial_graph_eq, this],
end

lemma real_qam.edges_eq_zero_iff {A : l(ℍ)} (hA : real_qam hφ.elim A) :
  hA.edges = 0 ↔ A = 0 :=
begin
  have : ∀ α β : ℕ, α = β ↔ (α : ℂ) = (β : ℂ),
  { intros α β,
    simp only [nat.cast_inj, iff_self], },
  refine ⟨λ h, _, λ h,
    by rw [this, real_qam.edges_eq, h, linear_map.zero_apply, trace_zero]; norm_cast⟩,
  rw [real_qam.edges] at h,
  have h' := h,
  simp only [finrank_eq_zero] at h,
  rw [qam.idempotent_and_real.eq hA.1 hA.2],
  let u := (qam.onb_of_idempotent_and_real hA.1 hA.2),
  apply finset.sum_eq_zero,
  intros i hi,
  rw [finrank_zero_iff_forall_zero.mp h' (u i)],
  norm_cast,
  simp_rw [matrix.zero_mul, linear_map.mul_left_zero_eq_zero, zero_mul],
end

private lemma orthogonal_projection_of_top {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] :
  orthogonal_projection' (⊤ : submodule 𝕜 E) = 1 :=
begin
  ext1,
  simp_rw [continuous_linear_map.one_apply, orthogonal_projection'_apply],
  rw orthogonal_projection_eq_self_iff,
  simp only [submodule.mem_top],
end

lemma Psi_apply_complete_graph {t s : ℝ} :
  hφ.elim.Psi t s (|(1 : ℍ)⟩⟨(1 : ℍ)|) = 1 :=
begin
  simp only [linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply, _root_.map_one, conj_transpose_one],
  refl,
end

lemma real_qam.edges_eq_dim_iff {A : l(ℍ)} (hA : real_qam hφ.elim A) :
  hA.edges = finite_dimensional.finrank ℂ (⊤ : submodule ℂ ℍ)
    ↔ A = (|(1 : ℍ)⟩⟨(1 : ℍ)|) :=
begin
  refine ⟨λ h, _, λ h, by { rw [← @qam.complete_graph_edges n _ _ φ],
    simp only [h] at hA,
    simp only [h, hA],
    refl, }⟩,
  rw real_qam.edges at h,
  simp only [finrank_top] at h,
  let U := (qam.submodule_of_idempotent_and_real hA.1 hA.2),
  have hU : U = (⊤ : submodule ℂ ℍ) := submodule.eq_top_of_finrank_eq h,
  rw ← function.injective.eq_iff (hφ.elim.Psi 0 (1/2)).injective,
  have t1 := qam.orthogonal_projection'_eq hA.1 hA.2,
  have : ((orthogonal_projection' U) : l(ℍ)) = 1,
  { rw [hU, orthogonal_projection_of_top],
    refl, },
  rw this at t1,
  apply_fun (one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] matrix (n × n) (n × n) ℂ)
    using (star_alg_equiv.injective _),
  simp_rw [Psi_apply_complete_graph, _root_.map_one, one_map_transpose_eq],
  rw [← function.injective.eq_iff hφ.elim.to_matrix.symm.injective,
    ← t1, _root_.map_one],
end


private lemma orthogonal_projection_of_dim_one {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  {U : submodule 𝕜 E} (hU : finite_dimensional.finrank 𝕜 U = 1) :
  ∃ v : {x : E // (x : E) ≠ 0}, orthogonal_projection' U
    = (1 / (‖(v : E)‖ ^ 2 : 𝕜)) • rank_one (v : E) (v : E) :=
begin
  let u : orthonormal_basis (fin 1) 𝕜 U,
  { rw ← hU,
    exact std_orthonormal_basis 𝕜 U },
  rw [orthonormal_basis.orthogonal_projection'_eq_sum_rank_one u, fin.sum_univ_one],
  have hcc : (u 0 : E) ≠ 0,
  { have := basis.ne_zero u.to_basis 0,
    simp_rw [orthonormal_basis.coe_to_basis] at this,
    simp only [ne.def, submodule.coe_eq_zero],
    exact this, },
  have : ‖((u 0 : E))‖ = 1,
  { rw [@norm_eq_sqrt_inner 𝕜, real.sqrt_eq_one],
    simp_rw [← submodule.coe_inner,
      orthonormal_iff_ite.mp u.orthonormal, eq_self_iff_true,
      if_true, is_R_or_C.one_re], },
  refine ⟨⟨u 0, hcc⟩, _⟩,
  simp only [subtype.coe_mk, this, is_R_or_C.of_real_one, one_div_one, one_smul, one_pow],
end

lemma real_qam.edges_eq_one_iff {A : l(ℍ)} (hA : real_qam hφ.elim A) :
  hA.edges = 1 ↔
    ∃ x : {x : ℍ // x ≠ 0}, A = (1 / (‖(x : ℍ)‖ ^ 2 : ℂ))
      • ((linear_map.mul_left ℂ ((x : ℍ) ⬝ φ.matrix)
      * (linear_map.mul_right ℂ (φ.matrix ⬝ (x : ℍ))).adjoint)) :=
begin
  split,
  { intros h,
    rw real_qam.edges at h,
    obtain ⟨u, hu⟩ := orthogonal_projection_of_dim_one h,
    have hu' : (u : ℍ) ≠ 0,
    { simp only [ne.def, submodule.coe_eq_zero],
      exact set.mem_set_of.mp (subtype.mem u), },
    use ⟨u, hu'⟩,
    have t1 := qam.orthogonal_projection'_eq hA.1 hA.2,
    simp_rw [← rank_one_to_matrix_transpose_Psi_symm, ← smul_hom_class.map_smul,
      subtype.coe_mk, ← rank_one_lm_eq_rank_one, ← smul_rank_one_lm, rank_one_lm_eq_rank_one,
      rank_one.apply_smul, ← hu, linear_equiv.eq_symm_apply, ← one_map_transpose_symm_eq,
      star_alg_equiv.eq_apply_iff_symm_eq, star_alg_equiv.symm_symm,
      alg_equiv.eq_apply_iff_symm_eq],
    exact t1.symm, },
  { rintros ⟨x, rfl⟩,
    letI := hφ.elim.matrix_is_pos_def.invertible,
    have ugh : ((x : ℍ) ⬝ φ.matrix ⬝ (x : ℍ)ᴴ).trace = ‖(x : ℍ)‖ ^ 2,
    { rw [← trace_mul_cycle, ← linear_map.is_faithful_pos_map.inner_eq',
        inner_self_eq_norm_sq_to_K], },
    have := real_qam.edges_eq hA,
    simp only [linear_map.smul_apply, trace_smul, linear_map.mul_apply,
      linear_map.matrix.mul_right_adjoint, linear_map.mul_left_apply,
      linear_map.mul_right_apply, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq,
      sig_apply_matrix_mul_pos_def', mul_eq_mul, inv_mul_cancel_left_of_invertible,
      ugh, smul_eq_mul, one_div] at this ⊢,
    have this' : ((‖(x : ℍ)‖ : ℝ) ^ 2 : ℂ) ≠ (0 : ℂ),
    {
      simp_rw [ne.def, sq_eq_zero_iff, complex.of_real_eq_zero, norm_eq_zero'],
      exact subtype.mem x,
      -- exact set.mem_set_of.mp (subtype.mem x),
      --},
       },
    rw [inv_mul_cancel this'] at this,
    norm_cast at this ⊢,
    -- exact this,
    rw [this],
      -- },
       },
end
