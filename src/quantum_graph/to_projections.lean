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

variables {p : Type*} [fintype p] [decidable_eq p] {n : p → Type*}
  [Π i, fintype (n i)] [Π i, decidable_eq (n i)]

open_locale tensor_product big_operators kronecker functional

-- local notation `ℍ` := matrix (n i) (n i) ℂ
local notation `ℍ` := matrix p p ℂ
local notation `ℍ_`i := matrix (n i) (n i) ℂ
-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

variables --{φ : Π i, module.dual ℂ (ℍ_ i)}
  --[hφ : ∀ i, fact (φ i).is_faithful_pos_map]
  {φ : module.dual ℂ ℍ} [hφ : fact φ.is_faithful_pos_map]

open_locale matrix
open matrix

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y
local notation `m` := linear_map.mul' ℂ ℍ
local notation `η` := algebra.linear_map ℂ ℍ
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `υ` :=
  ((tensor_product.assoc ℂ (ℍ) (ℍ) (ℍ))
    : (ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ) →ₗ[ℂ]
      ℍ ⊗[ℂ] (ℍ ⊗[ℂ] ℍ))
local notation `υ⁻¹` :=
  ((tensor_product.assoc ℂ (ℍ) (ℍ) (ℍ)).symm
    : ℍ ⊗[ℂ] (ℍ ⊗[ℂ] ℍ) →ₗ[ℂ]
      (ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ))
local notation `ϰ` := (↑(tensor_product.comm ℂ (ℍ) ℂ)
  : (ℍ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] ℍ))
local notation `ϰ⁻¹` := ((tensor_product.comm ℂ (ℍ) ℂ).symm
  : (ℂ ⊗[ℂ] ℍ) →ₗ[ℂ] (ℍ ⊗[ℂ] ℂ))
local notation `τ` := ((tensor_product.lid ℂ (ℍ))
  : (ℂ ⊗[ℂ] ℍ) →ₗ[ℂ] ℍ)
local notation `τ⁻¹` := ((tensor_product.lid ℂ (ℍ)).symm
  : ℍ →ₗ[ℂ] (ℂ ⊗[ℂ] ℍ))
local notation `id` := (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def block_diag'_kronecker_equiv
  {φ : Π i, module.dual ℂ (ℍ_ i)}
  (hφ : ∀ i, fact (φ i).is_faithful_pos_map) :
    matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ
    ≃ₗ[ℂ]
    { x : matrix (Σ i, n i) (Σ i, n i) ℂ // x.is_block_diagonal }
    ⊗[ℂ]
    { x : matrix (Σ i, n i) (Σ i, n i) ℂ // x.is_block_diagonal }
    :=
((module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hφ i).elim)).symm.to_linear_equiv.trans
    ((module.dual.pi.is_faithful_pos_map.Psi hφ 0 0).trans
      (linear_equiv.tensor_product.map (1 : (Π i, matrix (n i) (n i) ℂ) ≃ₗ[ℂ] _)
        ((pi.transpose_alg_equiv p n : _ ≃ₐ[ℂ] _ᵐᵒᵖ).symm).to_linear_equiv))).trans
    (linear_equiv.tensor_product.map (is_block_diagonal_pi_alg_equiv.symm.to_linear_equiv)
    (is_block_diagonal_pi_alg_equiv.symm.to_linear_equiv))

lemma linear_equiv.coe_one {R : Type*} [semiring R] (M : Type*) [add_comm_monoid M]
  [module R M] :
  ↑(1 : M ≃ₗ[R] M) = (1 : M →ₗ[R] M) :=
rfl

lemma matrix.conj_conj_transpose' {R n₁ n₂ : Type*} [has_involutive_star R] (A : matrix n₁ n₂ R) :
  ((Aᴴ)ᵀ)ᴴ = Aᵀ :=
by rw [← conj_conj_transpose A]; refl

lemma to_matrix_mul_left_mul_right_adjoint {φ : Π i, module.dual ℂ (matrix (n i) (n i) ℂ)}
  (hφ : Π i, fact (φ i).is_faithful_pos_map) (x y : Π i, (ℍ_ i)) :
  (module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hφ i).elim))
    ((linear_map.mul_left ℂ x) * ((linear_map.mul_right ℂ y).adjoint : l(Π i, ℍ_ i)))
  = block_diagonal' (λ i, (x i) ⊗ₖ ((hφ i).elim.sig (1/2) (y i))ᴴᵀ) :=
begin
  have : (1 / 2 : ℝ) + (-1 : ℝ) = - (1 / 2) := by norm_num,
  simp_rw [_root_.map_mul, ← lmul_eq_mul, ← rmul_eq_mul,
    rmul_adjoint, pi_lmul_to_matrix, pi_rmul_to_matrix,
    mul_eq_mul, ← block_diagonal'_mul, ← mul_kronecker_mul,
    matrix.one_mul, matrix.mul_one, module.dual.pi.is_faithful_pos_map.sig_eq_pi_blocks,
    pi.star_apply, module.dual.is_faithful_pos_map.sig_apply_sig, star_eq_conj_transpose,
    this, ← module.dual.is_faithful_pos_map.sig_conj_transpose],
  refl,
end

@[instance] private def smul_comm_class_aux {ι₂ : Type*} {E₂ : ι₂ → Type*} [Π i, add_comm_monoid (E₂ i)] [Π i, module ℂ (E₂ i)] :
  ∀ (i : ι₂), smul_comm_class ℂ ℂ (E₂ i) :=
λ i, by apply_instance

@[simps] def pi.linear_map.apply {ι₁ ι₂ : Type*} {E₁ : ι₁ → Type*}
  [decidable_eq ι₁] [fintype ι₁]
  [Π i, add_comm_monoid (E₁ i)] [Π i, module ℂ (E₁ i)]
  {E₂ : ι₂ → Type*} [Π i, add_comm_monoid (E₂ i)] [Π i, module ℂ (E₂ i)]
  (i : ι₁) (j : ι₂) :
  ((Π a, E₁ a) →ₗ[ℂ] (Π a, E₂ a)) →ₗ[ℂ] (E₁ i →ₗ[ℂ] E₂ j) :=
{ to_fun := λ x,
  { to_fun := λ a, (x ((linear_map.single i : E₁ i →ₗ[ℂ] Π b, E₁ b) a)) j,
    map_add' := λ a b, by
    { simp only [linear_map.add_apply, map_add, pi.add_apply], },
    map_smul' := λ c a, by
    { simp only [linear_map.smul_apply, linear_map.map_smul, pi.smul_apply, ring_hom.id_apply], } },
  map_add' := λ x y, by
  { ext a,
    simp only [linear_map.add_apply, pi.add_apply, linear_map.coe_mk], },
  map_smul' := λ c x, by
  { ext a,
    simp only [linear_map.smul_apply, pi.smul_apply, linear_map.map_smul, ring_hom.id_apply,
      linear_map.coe_mk], } }

lemma rank_one_Psi_transpose_to_lin {n : Type*} [decidable_eq n] [fintype n]
  {φ : module.dual ℂ (matrix n n ℂ)} [hφ : fact (φ.is_faithful_pos_map)]
  (x y : matrix n n ℂ) :
  hφ.elim.to_matrix.symm
  ((tensor_product.map (1 : l(matrix n n ℂ))
      (transpose_alg_equiv n ℂ ℂ).symm.to_linear_map)
    ((hφ.elim.Psi 0 (1/2)) (|x⟩⟨y|))).to_kronecker
  = (linear_map.mul_left ℂ x) * ((linear_map.mul_right ℂ y).adjoint : l(matrix n n ℂ)) :=
begin
  let b := @module.dual.is_faithful_pos_map.orthonormal_basis n _ _ φ _,
  rw ← function.injective.eq_iff hφ.elim.to_matrix.injective,
  simp_rw [_root_.map_mul, linear_map.matrix.mul_right_adjoint, linear_map.mul_right_to_matrix,
    linear_map.mul_left_to_matrix, matrix.mul_eq_mul, ← mul_kronecker_mul, matrix.one_mul,
    matrix.mul_one, module.dual.is_faithful_pos_map.sig_apply_sig],
  have : (1 / 2 : ℝ) + -1 = - (1 / 2) := by norm_num,
  rw [this, ← module.dual.is_faithful_pos_map.sig_conj_transpose, alg_equiv.apply_symm_apply,
    module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    module.dual.is_faithful_pos_map.Psi_to_fun'_apply, tensor_product.map_tmul,
    tensor_product.to_kronecker_apply, module.dual.is_faithful_pos_map.sig_zero,
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

-- example :
--   -- { x : matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ // x.is_block_diagonal }
--   matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ
--     ≃ₐ[ℂ]
--   { x : matrix (Σ i : p × p, n i.1 × n i.2) (Σ i : p × p, n i.1 × n i.2) ℂ // x.is_block_diagonal }
--   -- {x : (matrix (Σ i, n i) (Σ i, n i) ℂ) ⊗[ℂ] (matrix (Σ i, n i) (Σ i, n i) ℂ) // x.is_block_diagonal}
--   -- {x : matrix (Σ i, n i) (Σ i, n i) ℂ // x.is_block_diagonal} :=
--   -- (Π i, matrix (n i) (n i) ℂ) ⊗[ℂ] (Π i, matrix (n i) (n i) ℂ)
--   :=
-- { to_fun := λ x, by {  },
--   -- dite (a.1.1 = b.1.1)
--   -- (λ h1,
--   --   dite (a.1.1 = a.2.1 ∧ b.1.1 = b.2.1) (
--   --   λ h : a.1.1 = a.2.1 ∧ b.1.1 = b.2.1,
--   --   let a' : n a.1.1 := by rw [h.1]; exact a.2.2 in
--   --   let b' : n b.1.1 := by rw [h.2]; exact b.2.2 in
--   --   x (⟨a.1.1, a.1.2, a'⟩) (⟨b.1.1, b.1.2, b'⟩))
--   -- (λ h, 0),
--   inv_fun := λ x a b, x (⟨a.1, a.2.1⟩, ⟨a.1, a.2.2⟩) (⟨b.1, b.2.1⟩, ⟨b.1, b.2.2⟩),
--   left_inv := λ x, by
--   { ext1,
--     simp only [],
--     split_ifs,
--     tidy, },
--   right_inv := λ x, by
--   { ext1,
--     simp only [],
--     split_ifs,
--     tidy, },
--      }

lemma rank_one_to_matrix_transpose_Psi_symm
  (x y : ℍ) :
  (hφ.elim.Psi 0 (1/2)).symm ((tensor_product.map id (transpose_alg_equiv p ℂ ℂ).to_linear_map)
      (hφ.elim.to_matrix (|x⟩⟨y|)).kronecker_to_tensor_product)
  = (linear_map.mul_left ℂ (x ⬝ φ.matrix))
    * ((linear_map.mul_right ℂ (φ.matrix ⬝ y)).adjoint : l(ℍ)) :=
begin
  rw kmul_representation (hφ.elim.to_matrix (|x⟩⟨y|)),
  simp_rw [map_sum, smul_hom_class.map_smul, kronecker_to_tensor_product_apply,
    tensor_product.map_tmul, linear_map.one_apply, alg_equiv.to_linear_map_apply,
    transpose_alg_equiv_apply, module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_symm_mk,
    module.dual.is_faithful_pos_map.Psi_inv_fun'_apply, unop, linear_equiv.coe_coe,
    mul_opposite.coe_op_linear_equiv_symm, mul_opposite.unop_op,
    matrix.std_basis_matrix.transpose', std_basis_matrix_conj_transpose,
    neg_zero, module.dual.is_faithful_pos_map.sig_zero, star_one,
    linear_map.matrix.mul_right_adjoint, linear_map.ext_iff, linear_map.sum_apply,
    linear_map.mul_apply, linear_map.smul_apply, continuous_linear_map.coe_coe,
    rank_one_apply, rank_one_to_matrix, conj_transpose_col, ← vec_mul_vec_eq,
    vec_mul_vec_apply, pi.star_apply, linear_map.mul_left_apply, linear_map.mul_right_apply,
    reshape_apply],
  have : ∀ (i j : p) (a : ℍ), ⟪hφ.elim.sig (-(1/2)) e_{i,j}, a⟫_ℂ
    = ⟪e_{i,j} ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2)), hφ.elim.matrix_is_pos_def.rpow (1/2) ⬝ a⟫_ℂ,
  { intros i j a,
    simp_rw [module.dual.is_faithful_pos_map.sig_apply, matrix.mul_assoc, neg_neg,
      ← module.dual.is_faithful_pos_map.basis_apply hφ.elim (i,j),
      module.dual.is_faithful_pos_map.inner_left_mul,
      module.dual.is_faithful_pos_map.inner_coord', (pos_def.rpow.is_hermitian _ _).eq], },
  intros a,
  simp_rw [this, ← hφ.elim.basis_apply (_,_), module.dual.is_faithful_pos_map.inner_coord',
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

lemma matrix.conj_eq_transpose_conj_transpose {R n₁ n₂ : Type*} [has_star R] (A : matrix n₁ n₂ R) :
  Aᴴᵀ = Aᵀᴴ :=
rfl
lemma matrix.conj_eq_conj_transpose_transpose {R n₁ n₂ : Type*} [has_star R] (A : matrix n₁ n₂ R) :
  Aᴴᵀ = (Aᴴ)ᵀ :=
rfl

noncomputable def one_map_transpose :
  (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] (matrix (p × p) (p × p) ℂ) :=
star_alg_equiv.of_alg_equiv ( (alg_equiv.tensor_product.map (1 : ℍ ≃ₐ[ℂ] ℍ)
          (transpose_alg_equiv p ℂ ℂ).symm).trans tensor_to_kronecker)
(begin
  intro x,
  simp only [alg_equiv.trans_apply],
  apply x.induction_on,
  { simp only [star_zero, map_zero], },
  { intros x₁ x₂,
    let x₂' : ℍ := mul_opposite.unop x₂,
    have : x₂ = mul_opposite.op x₂' := rfl,
    simp only [tensor_product.star_tmul,
      alg_equiv.tensor_product.map,
      alg_equiv.coe_mk, algebra.tensor_product.map_tmul,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom,
      alg_equiv.one_apply],
    simp_rw [this, ← mul_opposite.op_star, transpose_alg_equiv_symm_op_apply,
      tensor_to_kronecker, alg_equiv.coe_mk,
      tensor_product.to_kronecker_star, tensor_product.star_tmul,
      star_eq_conj_transpose,
      ← matrix.conj_eq_transpose_conj_transpose,
      ← matrix.conj_eq_conj_transpose_transpose], },
  { intros a b ha hb,
    simp only [map_add, star_add, ha, hb], },
end)

lemma one_map_transpose_eq (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
  (one_map_transpose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _) x = ((tensor_product.map (1 : l(ℍ))
    (transpose_alg_equiv p ℂ ℂ).symm.to_linear_map) x).to_kronecker :=
rfl
lemma one_map_transpose_symm_eq (x : matrix (p × p) (p × p) ℂ) :
  (one_map_transpose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _).symm x = ((tensor_product.map (1 : l(ℍ))
    (transpose_alg_equiv p ℂ ℂ).to_linear_map) x.kronecker_to_tensor_product) :=
rfl

lemma one_map_transpose_apply (x y : ℍ) :
  (one_map_transpose : _ ≃⋆ₐ[ℂ] matrix (p × p) (p × p) ℂ) (x ⊗ₜ mul_opposite.op y) = x ⊗ₖ yᵀ :=
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
  simp only [module.dual.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    pi.star_apply, star_apply, star_eq_conj_transpose, conj_transpose_apply,
    linear_map.star_eq_adjoint, linear_map.adjoint_inner_right, is_R_or_C.star_def,
    inner_conj_symm, module.dual.is_faithful_pos_map.basis_repr_apply],
end
private lemma ffsugh {x : matrix (p × p) (p × p) ℂ} {y : l(ℍ)} :
  hφ.elim.to_matrix.symm x = y ↔ x = hφ.elim.to_matrix y :=
equiv.symm_apply_eq _
lemma to_matrix''_symm_map_star (x : matrix (p × p) (p × p) ℂ) :
  hφ.elim.to_matrix.symm (star x) = ((hφ.elim.to_matrix.symm x).adjoint) :=
begin
  rw [ffsugh, to_matrix''_map_star, alg_equiv.apply_symm_apply],
end

lemma qam.idempotent_and_real_iff_exists_ortho_proj (A : l(ℍ)) :
  (qam.refl_idempotent hφ.elim A A = A ∧ A.is_real) ↔
    ∃ (U : submodule ℂ ℍ),
      (orthogonal_projection' U : l(ℍ))
      = (hφ.elim.to_matrix.symm ((tensor_product.map id (transpose_alg_equiv p ℂ ℂ).symm.to_linear_map)
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
  = (hφ.elim.to_matrix.symm ((tensor_product.map id (transpose_alg_equiv p ℂ ℂ).symm.to_linear_map)
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
    by { simp_rw [module.dual.is_faithful_pos_map.inner_eq'],
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
  real_qam hφ.elim (qam.complete_graph ℍ) :=
⟨qam.nontracial.complete_graph.qam, qam.nontracial.complete_graph.is_real⟩

lemma qam.complete_graph_edges :
  (@complete_graph_real_qam p _ _ φ hφ).edges = finite_dimensional.finrank ℂ (⊤ : submodule ℂ ℍ) :=
begin
  have := calc
    (real_qam.edges complete_graph_real_qam : ℂ)
    = (qam.complete_graph ℍ φ.matrix⁻¹).trace : real_qam.edges_eq _,
  haveI ig := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [qam.complete_graph, continuous_linear_map.coe_coe,
    rank_one_apply, module.dual.is_faithful_pos_map.inner_eq',
    conj_transpose_one, matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one] at this,
  norm_cast at this,
  simp_rw [qam.complete_graph, this, finrank_top, finite_dimensional.finrank_matrix],
end

lemma qam.trivial_graph_real_qam [nontrivial p] :
  real_qam hφ.elim (qam.trivial_graph hφ rfl) :=
⟨qam.nontracial.trivial_graph.qam rfl, qam.nontracial.trivial_graph.is_real rfl⟩

lemma qam.trivial_graph_edges [nontrivial p] :
  (@qam.trivial_graph_real_qam p _ _ φ hφ _).edges = 1 :=
begin
  have := real_qam.edges_eq (@qam.trivial_graph_real_qam p _ _ φ _ _),
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

lemma orthogonal_projection_of_top {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [complete_space ↥(⊤ : submodule 𝕜 E)] :
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
  simp only [module.dual.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    module.dual.is_faithful_pos_map.Psi_to_fun'_apply, _root_.map_one, conj_transpose_one],
  refl,
end

lemma real_qam.edges_eq_dim_iff {A : l(ℍ)} (hA : real_qam hφ.elim A) :
  hA.edges = finite_dimensional.finrank ℂ (⊤ : submodule ℂ ℍ)
    ↔ A = (|(1 : ℍ)⟩⟨(1 : ℍ)|) :=
begin
  refine ⟨λ h, _, λ h, by { rw [← @qam.complete_graph_edges p _ _ φ],
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
  apply_fun (one_map_transpose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] matrix (p × p) (p × p) ℂ)
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
    { rw [← trace_mul_cycle, ← module.dual.is_faithful_pos_map.inner_eq',
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
