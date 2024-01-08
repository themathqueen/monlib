/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.mul''
import linear_algebra.my_matrix.pos_def_rpow
import linear_algebra.inner_aut
import linear_algebra.my_matrix.reshape
import linear_algebra.to_matrix_of_equiv
import linear_algebra.my_ips.tensor_hilbert
import linear_algebra.my_ips.functional
import linear_algebra.my_ips.mat_ips
import linear_algebra.my_ips.mul_op
import linear_algebra.my_matrix.include_block
import linear_algebra.my_ips.op_unop

/-!

# Some results on the Hilbert space on C*-algebras

This file contains some results on the Hilbert space on C*-algebras.

-/

variables {n : Type*} [fintype n]

local notation `ℍ` := matrix n n ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)
local notation `⟪` x `,` y `⟫` := @inner ℂ _ _ x y

open_locale matrix

open matrix

variables [decidable_eq n] {φ : matrix n n ℂ →ₗ[ℂ] ℂ}
  [hφ : fact φ.is_faithful_pos_map]
  {k : Type*} [fintype k] [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)]
  [Π i, decidable_eq (s i)] {ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]

local notation `ℍ₂` := Π i, matrix (s i) (s i) ℂ

open_locale kronecker matrix big_operators tensor_product

section single_block

/-! # Section single_block -/

lemma inner_std_basis_matrix_left [hφ : fact φ.is_faithful_pos_map]
  (i j : n) (x : matrix n n ℂ) :
  ⟪(std_basis_matrix i j (1 : ℂ)), x⟫_ℂ = (x ⬝ φ.matrix) i j :=
begin
  simp only [linear_map.is_faithful_pos_map.inner_eq',
    std_basis_matrix_conj_transpose, star_one],
  rw [matrix.mul_assoc, ← trace_mul_cycle', matrix.std_basis_matrix_mul_trace],
end

lemma inner_std_basis_matrix_std_basis_matrix [hφ : fact φ.is_faithful_pos_map]
  (i j k l : n) :
  ⟪(std_basis_matrix i j (1 : ℂ)), (std_basis_matrix k l (1 : ℂ))⟫_ℂ
    = ite (i = k) (φ.matrix l j) 0 :=
begin
  simp_rw [inner_std_basis_matrix_left, mul_apply, std_basis_matrix, boole_mul, ite_and],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero,
    finset.sum_ite_eq, finset.mem_univ, if_true, finset.sum_ite_eq],
  simp_rw @eq_comm _ (k : n) (i : n),
end

/-- we can expres the nontracial adjoint of `linear_map.mul'` by
  $$m^*(x) = \sum_{i,j,k,l} x_{il}Q^{-1}_{kj}(e_{ij} \otimes_t e_{kl})$$ -/
lemma linear_map.mul'_adjoint [hφ : fact φ.is_faithful_pos_map]
  (x : matrix n n ℂ) :
  (linear_map.mul' ℂ ℍ).adjoint x = ∑ (i j k l : n), (x i l * φ.matrix⁻¹ k j)
    • (std_basis_matrix i j 1 ⊗ₜ[ℂ] std_basis_matrix k l 1) :=
begin
  apply @ext_inner_left ℂ _ _,
  intros v,
  rw linear_map.adjoint_inner_right,
  rw v.matrix_eq_sum_std_basis,
  simp_rw [map_sum, smul_hom_class.map_smul, linear_map.mul'_apply, sum_inner, inner_sum,
    mul_eq_mul, std_basis_matrix_mul, inner_smul_left, inner_smul_right, star_ring_end_apply,
    star_ite, one_mul, star_one, star_zero, boole_mul, mul_ite, mul_zero],
  simp only [finset.sum_ite_irrel, finset.sum_ite_eq, finset.sum_ite_eq',
    finset.sum_const_zero, finset.mem_univ, if_true, tensor_product.inner_tmul],
  simp only [inner_std_basis_matrix_std_basis_matrix, ite_mul, mul_ite, mul_zero, zero_mul,
    finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ,
    if_true, finset.sum_ite_eq'],
  simp only [inner_std_basis_matrix_left, ← finset.mul_sum],
  have : ∀ x_1 x_2 x_3 x_4 : n,
    ∑ (x_5 x_6 : n), x x_1 x_6 * (φ.matrix)⁻¹ x_3 x_5 * (φ.matrix x_5 x_2 * φ.matrix x_6 x_4)
    = (φ.matrix⁻¹ ⬝ φ.matrix) x_3 x_2 * (x ⬝ φ.matrix) x_1 x_4,
  { intros i j k l,
    simp only [mul_apply, finset.sum_mul, finset.mul_sum],
    rw finset.sum_comm,
    repeat { apply finset.sum_congr rfl, intros, },
    ring_nf, },
  haveI hm := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [this, inv_mul_of_invertible, one_apply, boole_mul, mul_ite, mul_zero,
    finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq', finset.mem_univ, if_true],
end

lemma matrix.linear_map_ext_iff_inner_map [hφ : fact φ.is_faithful_pos_map]
  {x y : l(ℍ)} :
  x = y ↔ ∀ u v : ℍ, ⟪x u, v⟫_ℂ = ⟪y u, v⟫_ℂ :=
begin
  simp_rw [linear_map.ext_iff],
  refine ⟨λ h u v, by rw h, λ h a, _⟩,
  apply @_root_.ext_inner_right ℂ _ _,
  exact h _,
end

lemma matrix.linear_map_ext_iff_map_inner [hφ : fact φ.is_faithful_pos_map] {x y : l(ℍ)} :
  x = y ↔ ∀ u v : ℍ, ⟪v, x u⟫_ℂ = ⟪v, y u⟫_ℂ :=
begin
  rw @matrix.linear_map_ext_iff_inner_map n _ _ φ,
  simp_rw [← inner_product_space.core.inner_conj_symm _ (x _),
    ← inner_product_space.core.inner_conj_symm (y _) _],
  exact ⟨λ h u v, by rw [h, star_ring_end_self_apply],
    λ h u v, by rw [← h, star_ring_end_self_apply]⟩,
end

open_locale matrix

lemma matrix.inner_conj_Q [hφ : fact φ.is_faithful_pos_map]
  (a x : ℍ) :
  ⟪x, φ.matrix ⬝ a ⬝ φ.matrix⁻¹⟫_ℂ = ⟪x ⬝ aᴴ, 1⟫_ℂ :=
begin
  simp_rw [linear_map.is_faithful_pos_map.inner_eq', ← matrix.mul_assoc],
  rw matrix.trace_mul_cycle,
  simp_rw [← matrix.mul_assoc, @inv_mul_of_invertible n ℂ _ _ _ φ.matrix
      hφ.elim.matrix_is_pos_def.invertible, matrix.one_mul,
    conj_transpose_mul, matrix.mul_one, conj_transpose_conj_transpose],
  rw [← matrix.trace_mul_cycle, matrix.mul_assoc],
end

lemma matrix.inner_star_right [hφ : fact φ.is_faithful_pos_map]
  (b y : ℍ) :
  ⟪b, y⟫_ℂ = ⟪1, bᴴ ⬝ y⟫_ℂ :=
begin
  simp_rw [linear_map.is_faithful_pos_map.inner_eq', ← matrix.mul_assoc,
    conj_transpose_one, matrix.mul_one],
end

lemma matrix.inner_star_left [hφ : fact φ.is_faithful_pos_map] (a x : ℍ) :
  ⟪a, x⟫_ℂ = ⟪xᴴ ⬝ a, 1⟫_ℂ :=
begin
  rw [← inner_product_space.core.inner_conj_symm, matrix.inner_star_right,
    inner_product_space.core.inner_conj_symm],
end

lemma one_inner [hφ : fact φ.is_faithful_pos_map] (a : ℍ) :
  ⟪1, a⟫_ℂ = (φ.matrix ⬝ a).trace :=
by rw [linear_map.is_faithful_pos_map.inner_eq', conj_transpose_one, matrix.mul_one]

lemma linear_map.is_faithful_pos_map.map_star (hφ : φ.is_faithful_pos_map) (x : ℍ) :
  φ (star x) = star (φ x) :=
hφ.1.is_real x

lemma nontracial.unit_adjoint_eq [hφ : fact φ.is_faithful_pos_map] :
  (algebra.linear_map ℂ ℍ : ℂ →ₗ[ℂ] ℍ).adjoint = φ :=
begin
  rw [← @linear_map.is_faithful_pos_map.adjoint_eq n _ _ φ, linear_map.adjoint_adjoint],
end

local notation `m` := linear_map.mul' ℂ ℍ

lemma qam.nontracial.mul_comp_mul_adjoint [hφ : fact φ.is_faithful_pos_map] :
  (linear_map.mul' ℂ ℍ) ∘ₗ (linear_map.mul' ℂ ℍ).adjoint = (φ.matrix⁻¹).trace • 1 :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, ← matrix.ext_iff,
    linear_map.mul'_adjoint, map_sum, smul_hom_class.map_smul, linear_map.mul'_apply,
    finset.sum_apply, linear_map.smul_apply, pi.smul_apply, smul_eq_mul,
    linear_map.one_apply, mul_eq_mul, mul_apply, std_basis_matrix, boole_mul, finset.mul_sum,
    mul_ite, mul_zero, mul_one, ite_and],
  intros x i j,
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq,
    finset.sum_ite_eq', finset.mem_univ, if_true],
  simp_rw [← finset.mul_sum, ← trace_iff φ.matrix⁻¹, mul_comm],
end

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y

lemma linear_map.is_faithful_pos_map.inner_coord'
  [hφ : fact φ.is_faithful_pos_map]
  (ij : n × n) (x : ℍ) :
  ⟪hφ.elim.basis ij, x⟫_ℂ = (x ⬝ hφ.elim.matrix_is_pos_def.rpow (1 / 2)) ij.1 ij.2 :=
by rw [linear_map.is_faithful_pos_map.basis_apply,
  ← linear_map.is_faithful_pos_map.orthonormal_basis_apply,
  linear_map.is_faithful_pos_map.inner_coord ij x]

lemma rank_one_to_matrix (a b : matrix n n ℂ) :
  hφ.elim.to_matrix (|a⟩⟨b| : l(ℍ))
    = col (reshape (a ⬝ hφ.elim.matrix_is_pos_def.rpow (1 / 2)))
      ⬝ (col (reshape (b ⬝ hφ.elim.matrix_is_pos_def.rpow (1 / 2))))ᴴ :=
begin
  -- letI := hφ.normed_add_comm_group,
  ext1 i j,
  simp_rw [linear_map.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    continuous_linear_map.coe_coe, rank_one_apply, smul_hom_class.map_smul,
    finsupp.smul_apply, linear_map.is_faithful_pos_map.basis_repr_apply,
    ← inner_conj_symm b, linear_map.is_faithful_pos_map.inner_coord', smul_eq_mul,
    mul_comm, conj_transpose_col, ← vec_mul_vec_eq, vec_mul_vec_apply,
    pi.star_apply, reshape_apply, is_R_or_C.star_def],
end

noncomputable def linear_map.is_faithful_pos_map.sig
  (hφ : φ.is_faithful_pos_map)
  (z : ℝ) :
  matrix n n ℂ ≃ₐ[ℂ] matrix n n ℂ :=
{ to_fun := λ a, hφ.matrix_is_pos_def.rpow (-z) ⬝ a ⬝ hφ.matrix_is_pos_def.rpow (z),
  inv_fun := λ a, hφ.matrix_is_pos_def.rpow z ⬝ a ⬝ hφ.matrix_is_pos_def.rpow (-z),
  left_inv := λ a, by { simp_rw [matrix.mul_assoc, pos_def.rpow_mul_rpow, ← matrix.mul_assoc,
    pos_def.rpow_mul_rpow, add_neg_self, pos_def.rpow_zero, matrix.one_mul, matrix.mul_one], },
  right_inv := λ a, by { simp_rw [matrix.mul_assoc, pos_def.rpow_mul_rpow, ← matrix.mul_assoc,
    pos_def.rpow_mul_rpow, neg_add_self, pos_def.rpow_zero, matrix.one_mul, matrix.mul_one], },
  map_add' := λ x y, by { simp_rw [matrix.mul_add, matrix.add_mul], },
  commutes' := λ r, by { simp_rw [algebra.algebra_map_eq_smul_one,
    matrix.mul_smul, matrix.smul_mul, matrix.mul_one, pos_def.rpow_mul_rpow,
    neg_add_self, pos_def.rpow_zero], },
  map_mul' := λ a b, by { simp_rw [mul_eq_mul, matrix.mul_assoc, ← matrix.mul_assoc
    (hφ.matrix_is_pos_def.rpow _), pos_def.rpow_mul_rpow, add_neg_self, pos_def.rpow_zero,
    matrix.one_mul], } }

lemma linear_map.is_faithful_pos_map.sig_apply (hφ : φ.is_faithful_pos_map) (z : ℝ) (x : ℍ) :
  hφ.sig z x = hφ.matrix_is_pos_def.rpow (-z) ⬝ x ⬝ hφ.matrix_is_pos_def.rpow (z) :=
rfl
lemma linear_map.is_faithful_pos_map.sig_symm_apply (hφ : φ.is_faithful_pos_map) (z : ℝ) (x : ℍ) :
  (hφ.sig z).symm x = hφ.matrix_is_pos_def.rpow z ⬝ x ⬝ hφ.matrix_is_pos_def.rpow (-z) :=
rfl
lemma linear_map.is_faithful_pos_map.sig_symm_eq (hφ : φ.is_faithful_pos_map) (z : ℝ) :
  (hφ.sig z).symm = hφ.sig (-z) :=
begin
  ext1,
  simp_rw [linear_map.is_faithful_pos_map.sig_apply hφ,
    linear_map.is_faithful_pos_map.sig_symm_apply hφ, neg_neg],
end

noncomputable def linear_map.is_faithful_pos_map.Psi_to_fun' (hφ : φ.is_faithful_pos_map)
  (t s : ℝ) :
  l(ℍ) →ₗ[ℂ] (ℍ ⊗[ℂ] ℍᵐᵒᵖ) :=
{ to_fun := λ x, ∑ i j k l,
    hφ.to_matrix x (i,j) (k,l) •
      (hφ.sig t (hφ.basis (i,j))) ⊗ₜ (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.sig s (hφ.basis (k,l)))ᴴ,
  map_add' := λ x y, by { simp_rw [map_add, dmatrix.add_apply, add_smul,
    finset.sum_add_distrib], },
  map_smul' := λ r x, by { simp_rw [smul_hom_class.map_smul, pi.smul_apply,
    smul_assoc, ring_hom.id_apply, finset.smul_sum], } }

lemma linear_map.is_faithful_pos_map.sig_conj_transpose (hφ : φ.is_faithful_pos_map)
  (t : ℝ) (x : ℍ) :
  (hφ.sig t x)ᴴ = hφ.sig (-t) xᴴ :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, conj_transpose_mul,
    (matrix.pos_def.rpow.is_hermitian _ _).eq, neg_neg, ← matrix.mul_assoc],
end

lemma linear_map.is_faithful_pos_map.Psi_to_fun'_apply [hφ : fact φ.is_faithful_pos_map]
  (t s : ℝ) (x y : ℍ) :
  hφ.elim.Psi_to_fun' t s (|x⟩⟨y|) = (hφ.elim.sig t x) ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.sig s y)ᴴ :=
begin
  simp_rw [linear_map.is_faithful_pos_map.Psi_to_fun', linear_map.coe_mk,
    linear_map.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    continuous_linear_map.coe_coe, rank_one_apply, smul_hom_class.map_smul,
    finsupp.smul_apply,
    ← inner_product_space.core.inner_conj_symm y,
    ← linear_map.is_faithful_pos_map.basis_repr_apply],
  simp_rw [← tensor_product.tmul_smul, smul_eq_mul, mul_comm (star_ring_end ℂ _), ← smul_smul,
    ← tensor_product.tmul_sum, ← finset.smul_sum, ← tensor_product.smul_tmul,
    ← tensor_product.sum_tmul, ← smul_hom_class.map_smul, star_ring_end_apply,
    ← conj_transpose_smul, ← smul_hom_class.map_smul, ← map_sum, ← conj_transpose_sum,
    ← map_sum, ← finset.sum_product', prod.mk.eta, finset.univ_product_univ],
  simp only [linear_map.is_faithful_pos_map.basis_repr_apply, ← rank_one_apply,
    ← continuous_linear_map.sum_apply, linear_map.is_faithful_pos_map.basis_apply,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply,
    rank_one.sum_orthonormal_basis_eq_id, continuous_linear_map.one_apply],
end

noncomputable def linear_map.is_faithful_pos_map.Psi_inv_fun'
  (hφ : φ.is_faithful_pos_map) (t s : ℝ) :
  (ℍ ⊗[ℂ] ℍᵐᵒᵖ) →ₗ[ℂ] l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, ∑ (i j : n × n) in finset.univ ×ˢ finset.univ,
    (((hφ.basis.tensor_product hφ.basis.mul_opposite).repr) x) (i,j)
      • |hφ.sig (-t) (hφ.basis (i.1, i.2))⟩⟨hφ.sig (-s) (hφ.basis (j.1, j.2))ᴴ|,
  map_add' := λ x y, by { simp_rw [map_add, finsupp.add_apply, add_smul,
    finset.sum_add_distrib], },
  map_smul' := λ r x, by { simp_rw [smul_hom_class.map_smul, finsupp.smul_apply, smul_assoc,
    ← finset.smul_sum, ring_hom.id_apply], } },
end

lemma linear_map.is_faithful_pos_map.basis_op_repr_apply
  (hφ : φ.is_faithful_pos_map) (x : ℍᵐᵒᵖ) (ij : n × n) :
  (hφ.basis.mul_opposite.repr x) ij = (((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) x ⬝ (hφ.matrix_is_pos_def.rpow (1/2))) ij.1 ij.2) :=
begin
  rw [basis.mul_opposite_repr_apply, unop, linear_equiv.coe_coe,
    mul_opposite.coe_op_linear_equiv_symm],
  letI := fact.mk hφ,
  rw [linear_map.is_faithful_pos_map.basis_repr_apply],
  exact linear_map.is_faithful_pos_map.inner_coord' _ _,
end


lemma linear_map.is_faithful_pos_map.Psi_inv_fun'_apply
  [hφ : fact φ.is_faithful_pos_map] (t s : ℝ) (x : ℍ) (y : ℍᵐᵒᵖ) :
  (hφ.elim.Psi_inv_fun' t s : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) →ₗ[ℂ] l(ℍ))
    (x ⊗ₜ y) = |hφ.elim.sig (-t) x⟩⟨hφ.elim.sig (-s) ((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) y)ᴴ| :=
begin
  let y' : matrix n n ℂ := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) y,
  have : y = (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) y' := rfl,
  simp_rw [this, linear_map.is_faithful_pos_map.Psi_inv_fun', linear_map.coe_mk,
    basis.tensor_product_repr_tmul_apply, linear_map.is_faithful_pos_map.basis_op_repr_apply,
    linear_map.is_faithful_pos_map.basis_repr_apply, ← smul_smul],
  have s_rank_one : ∀ (α : ℂ) (x y : ℍ), (|α • x⟩⟨y| : ℍ →ₗ[ℂ] ℍ) = α • ↑|x⟩⟨y|,
  { intros _ _ _,
    simp_rw rank_one.apply_smul,
    refl, },
  have rank_one_s : ∀ (α : ℂ) (x y : ℍ), (|x⟩⟨star_ring_end ℂ α • y| : ℍ →ₗ[ℂ] ℍ)
    = α • ↑|x⟩⟨y|,
  { intros _ _ _,
    simp_rw [rank_one.smul_apply, star_ring_end_self_apply],
    refl, },
  have rank_one_sumz : ∀ (x : ℍ) (y : (n × n) → ℍ), (|x⟩⟨∑ i : n × n, y i| : ℍ →ₗ[ℂ] ℍ)
    = ∑ i in finset.univ ×ˢ finset.univ, (|x⟩⟨y i| : ℍ →ₗ[ℂ] ℍ) :=
  λ α β, by { simp only [rank_one_sum, linear_map.ext_iff, continuous_linear_map.coe_coe,
    continuous_linear_map.sum_apply, linear_map.sum_apply,
    finset.univ_product_univ, eq_self_iff_true, forall_true_iff], },
  have sumz_rank_one : ∀ (x : (n × n) → ℍ) (y : ℍ), (|∑ i : n × n, x i⟩⟨y| : ℍ →ₗ[ℂ] ℍ)
    = ∑ i in finset.univ ×ˢ finset.univ, (|x i⟩⟨y| : ℍ →ₗ[ℂ] ℍ) :=
  λ α β, by { simp only [sum_rank_one, linear_map.ext_iff, continuous_linear_map.coe_coe,
    continuous_linear_map.sum_apply, linear_map.sum_apply,
    finset.univ_product_univ, eq_self_iff_true, forall_true_iff], },
  simp_rw [← rank_one_s (((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) ((op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) y') ⬝ _) _ _), ← s_rank_one,
    ← rank_one_sumz, ← sumz_rank_one, ← smul_hom_class.map_smul, ← map_sum,
    star_ring_end_apply, ← conj_transpose_smul, ← conj_transpose_sum,
    ← linear_map.is_faithful_pos_map.inner_coord, linear_map.is_faithful_pos_map.basis_apply,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply, ← orthonormal_basis.repr_apply_apply,
    orthonormal_basis.sum_repr],
end

lemma linear_map.is_faithful_pos_map.sig_apply_sig (hφ : φ.is_faithful_pos_map)
  (t s : ℝ) (x : matrix n n ℂ) :
  hφ.sig t (hφ.sig s x) = hφ.sig (t + s) x :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc,
    matrix.pos_def.rpow_mul_rpow, ← matrix.mul_assoc, matrix.pos_def.rpow_mul_rpow,
    neg_add, add_comm],
end

lemma linear_map.is_faithful_pos_map.sig_zero
  (hφ : φ.is_faithful_pos_map) (x : matrix n n ℂ) :
  hφ.sig 0 x = x :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, neg_zero, matrix.pos_def.rpow_zero,
    matrix.mul_one, matrix.one_mul],
end

lemma linear_map.is_faithful_pos_map.Psi_left_inv' (hφ : φ.is_faithful_pos_map)
  (t s : ℝ) (A : l(ℍ)) :
  (hφ.Psi_inv_fun' t s) (hφ.Psi_to_fun' t s A) = A :=
begin
  letI := fact.mk hφ,
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one A,
  simp_rw [map_sum,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    linear_map.is_faithful_pos_map.Psi_inv_fun'_apply, unop_op,
    conj_transpose_conj_transpose, linear_map.is_faithful_pos_map.sig_apply_sig,
    neg_add_self, linear_map.is_faithful_pos_map.sig_zero],
end

lemma linear_map.is_faithful_pos_map.Psi_right_inv' (hφ : φ.is_faithful_pos_map) (t s : ℝ) (x : matrix n n ℂ)
  (y : (matrix n n ℂ)ᵐᵒᵖ):
  (hφ.Psi_to_fun' t s) (hφ.Psi_inv_fun' t s (x ⊗ₜ y)) = x ⊗ₜ y :=
begin
  letI := fact.mk hφ,
  simp_rw [linear_map.is_faithful_pos_map.Psi_inv_fun'_apply,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply, linear_map.is_faithful_pos_map.sig_apply_sig,
    add_neg_self, linear_map.is_faithful_pos_map.sig_zero,
    conj_transpose_conj_transpose, op_unop],
end

private lemma foo_eq (hφ : φ.is_faithful_pos_map) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
  x = ∑ (i j : n × n) in finset.univ ×ˢ finset.univ,
    (((hφ.basis.tensor_product hφ.basis.mul_opposite).repr) x) (i,j)
      • (hφ.basis) i ⊗ₜ[ℂ] (hφ.basis.mul_opposite : basis (n × n) ℂ _) j :=
begin
  simp_rw [← finset.sum_product', finset.univ_product_univ, prod.mk.eta,
    ← basis.tensor_product_apply', basis.sum_repr],
end


/-- this defines the linear equivalence from linear maps on $M_n$ to $M_n\otimes M_n^\textnormal{op}$, i.e.,
  $$\Psi_{t,s}\colon \mathcal{L}(M_n) \cong_{\texttt{l}} M_n \otimes M_n^\textnormal{op}$$ -/
noncomputable def linear_map.is_faithful_pos_map.Psi (hφ : φ.is_faithful_pos_map) (t s : ℝ) :
  l(ℍ) ≃ₗ[ℂ] (ℍ ⊗[ℂ] ℍᵐᵒᵖ) :=
{ to_fun := λ x, hφ.Psi_to_fun' t s x,
  inv_fun := λ x, hφ.Psi_inv_fun' t s x,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ r x, smul_hom_class.map_smul _ _ _,
  left_inv := λ x, linear_map.is_faithful_pos_map.Psi_left_inv' hφ t s x,
  right_inv := λ x,
    begin
      rw [foo_eq hφ x],
      simp_rw [map_sum, smul_hom_class.map_smul, linear_map.is_faithful_pos_map.Psi_right_inv'],
    end }

lemma linear_map.mul_left_to_matrix (hφ : φ.is_faithful_pos_map) (x : matrix n n ℂ) :
  hφ.to_matrix (linear_map.mul_left ℂ x) = x ⊗ₖ 1 :=
begin
  letI := fact.mk hφ,
  ext1,
  simp_rw [linear_map.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    linear_map.mul_left_apply, matrix.mul_eq_mul, linear_map.is_faithful_pos_map.basis_repr_apply,
    linear_map.is_faithful_pos_map.inner_coord', linear_map.is_faithful_pos_map.basis_apply,
    matrix.mul_assoc, pos_def.rpow_mul_rpow, neg_add_self, pos_def.rpow_zero,
    matrix.mul_one, mul_apply, std_basis_matrix, kronecker_map, of_apply, one_apply,
    mul_boole, ite_and, finset.sum_ite_eq, finset.mem_univ, if_true, eq_comm],
end

lemma linear_map.mul_right_to_matrix (x : matrix n n ℂ) :
  hφ.elim.to_matrix (linear_map.mul_right ℂ x) = 1 ⊗ₖ (hφ.elim.sig (1/2) x)ᵀ :=
begin
  ext1,
  simp_rw [linear_map.is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_apply,
    linear_map.mul_right_apply, matrix.mul_eq_mul, linear_map.is_faithful_pos_map.basis_repr_apply,
    linear_map.is_faithful_pos_map.inner_coord'],
  simp_rw [mul_apply, kronecker_map, of_apply, one_apply,
    linear_map.is_faithful_pos_map.basis_apply, mul_apply, std_basis_matrix,
    boole_mul, transpose_apply, ite_and, finset.sum_ite_irrel, finset.sum_const_zero,
    finset.sum_ite_eq, finset.mem_univ, if_true, eq_comm],
  simp only [ite_mul, zero_mul, finset.sum_ite_irrel, finset.sum_const_zero],
  simp_rw [← mul_apply],
  refl,
end

end single_block

section direct_sum

/-! # Section direct_sum -/

local notation `ℍ_`i := matrix (s i) (s i) ℂ

lemma include_block_adjoint [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (x : Π j, matrix (s j) (s j) ℂ) :
  (include_block : (ℍ_ i) →ₗ[ℂ] ℍ₂).adjoint x = x i :=
begin
  apply @ext_inner_left ℂ _ _,
  intros a,
  rw [linear_map.adjoint_inner_right, linear_map.is_faithful_pos_map.include_block_left_inner],
end

instance pi.tensor_product_finite_dimensional :
  finite_dimensional ℂ (ℍ₂ ⊗[ℂ] ℍ₂) :=
finite_dimensional.of_finite_basis (basis.of_vector_space ℂ _)
  (basis.of_vector_space_index ℂ _).to_finite

open_locale functional

lemma direct_sum_inner_std_basis_matrix_left [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (i : k) (j l : s i) (x : ℍ₂) :
  ⟪block_diag' (std_basis_matrix (⟨i,j⟩ : Σ a, s a) (⟨i,l⟩ : Σ a, s a) (1 : ℂ)), x⟫_ℂ
    = (x i * (ψ i).matrix) j l :=
begin
  simp only [← include_block_apply_std_basis_matrix,
    linear_map.is_faithful_pos_map.include_block_left_inner,
    inner_std_basis_matrix_left],
  refl,
end

lemma eq_mpr_std_basis_matrix {i j : k} {b c : s j}
  (h₁ : i = j) :
  (by rw h₁; exact std_basis_matrix b c (1 : ℂ)
    : matrix (s i) (s i) ℂ)
  = std_basis_matrix (by rw h₁; exact b) (by rw h₁; exact c) (1 : ℂ) :=
begin
  finish,
end

lemma direct_sum_inner_std_basis_matrix_std_basis_matrix
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i j : k} (a b : s i) (c d : s j) :
  ⟪block_diag' (std_basis_matrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
    block_diag' (std_basis_matrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ
    = dite (i = j)
      (λ h, ite (a = (by rw [h]; exact c))
        ((ψ i).matrix (by rw [h]; exact d) b) 0)
      (λ h, 0) :=
begin
  simp only [← include_block_apply_std_basis_matrix],
  by_cases i = j,
  { simp only [h, dif_pos, linear_map.is_faithful_pos_map.include_block_inner_same' h,
      inner_std_basis_matrix_std_basis_matrix, eq_mpr_std_basis_matrix h], },
  { simp only [h, dif_neg, not_false_iff, linear_map.is_faithful_pos_map.include_block_inner_ne_same h], },
end

lemma direct_sum_inner_std_basis_matrix_std_basis_matrix_same
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (a b c d : s i) :
  ⟪block_diag' (std_basis_matrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
    block_diag' (std_basis_matrix ⟨i, c⟩ ⟨i, d⟩ (1 : ℂ))⟫_ℂ
    = ite (a = c) ((ψ i).matrix d b) 0 :=
by rw [direct_sum_inner_std_basis_matrix_std_basis_matrix]; finish

lemma direct_sum_inner_std_basis_matrix_std_basis_matrix_ne
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i j : k} (h : i ≠ j) (a b : s i) (c d : s j) :
  ⟪block_diag' (std_basis_matrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
    block_diag' (std_basis_matrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ = 0 :=
by rw [direct_sum_inner_std_basis_matrix_std_basis_matrix]; finish

lemma linear_map.mul'_adjoint_single_block
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (x : matrix (s i) (s i) ℂ) :
  (linear_map.mul' ℂ ℍ₂).adjoint (include_block x)
    = (tensor_product.map include_block include_block)
      ((linear_map.mul' ℂ (ℍ_ i)).adjoint x) :=
begin
  rw tensor_product.inner_ext_iff',
  intros a b,
  rw [linear_map.adjoint_inner_left, linear_map.mul'_apply,
    linear_map.is_faithful_pos_map.include_block_left_inner,
    ← linear_map.adjoint_inner_right, tensor_product.map_adjoint,
    tensor_product.map_tmul,
    linear_map.adjoint_inner_left, linear_map.mul'_apply],
  simp_rw [include_block_adjoint, pi.mul_apply],
end

lemma linear_map.mul'_direct_sum_adjoint [hψ : Π i, fact (ψ i).is_faithful_pos_map] (x : ℍ₂) :
  (linear_map.mul' ℂ ℍ₂).adjoint x = ∑ (r : k) a b c d, (x r a d * (linear_map.direct_sum_matrix_block ψ r)⁻¹ c b)
    • block_diag' (std_basis_matrix (⟨r,a⟩ : Σ i, s i) (⟨r,b⟩ : Σ i, s i) (1 : ℂ))
      ⊗ₜ[ℂ]
      block_diag' (std_basis_matrix (⟨r,c⟩ : Σ i, s i) (⟨r,d⟩ : Σ i, s i) (1 : ℂ)) :=
begin
  nth_rewrite_lhs 0 [matrix_eq_sum_include_block x],
  simp_rw [map_sum, linear_map.mul'_adjoint_single_block],
  apply finset.sum_congr rfl, intros,
  rw [linear_map.mul'_adjoint],
  simp_rw [map_sum, smul_hom_class.map_smul, tensor_product.map_tmul,
    include_block_apply_std_basis_matrix, linear_map.direct_sum_matrix_block_apply],
end

lemma linear_map.mul'_direct_sum_apply_include_block
  {i : k} (x : (ℍ_ i) ⊗[ℂ] (ℍ_ i)) :
  linear_map.mul' ℂ ℍ₂ ((tensor_product.map include_block include_block) x)
    = include_block (linear_map.mul' ℂ (ℍ_ i) x) :=
begin
  simp_rw [← linear_map.comp_apply],
  revert x,
  rw [← linear_map.ext_iff, tensor_product.ext_iff],
  intros x y,
  simp only [linear_map.comp_apply, tensor_product.map_tmul, linear_map.mul'_apply,
    include_block_mul_same],
end

private lemma linear_map.mul'_comp_mul_adjoint_direct_sum_aux [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (x : ℍ_ i) :
  linear_map.mul' ℂ ℍ₂ ((linear_map.mul' ℂ ℍ₂).adjoint (include_block x)) = (ψ i).matrix⁻¹.trace • include_block x :=
begin
  rw [linear_map.mul'_adjoint_single_block, linear_map.mul'_direct_sum_apply_include_block],
  simp_rw [← linear_map.comp_apply, qam.nontracial.mul_comp_mul_adjoint, linear_map.comp_apply,
    linear_map.smul_apply, smul_hom_class.map_smul, linear_map.one_apply],
end

lemma linear_map.mul'_comp_mul'_adjoint_direct_sum [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x : ℍ₂) :
  linear_map.mul' ℂ ℍ₂ ((linear_map.mul' ℂ ℍ₂).adjoint (x)) = ∑ i, (ψ i).matrix⁻¹.trace • include_block (x i) :=
begin
  nth_rewrite 0 [matrix_eq_sum_include_block x],
  simp_rw [map_sum, linear_map.mul'_comp_mul_adjoint_direct_sum_aux],
end

lemma linear_map.mul'_comp_mul'_adjoint_direct_sum_eq_smul_id_iff
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  [Π i, nontrivial (s i)]
  (α : ℂ) :
  linear_map.mul' ℂ ℍ₂ ∘ₗ (linear_map.mul' ℂ ℍ₂).adjoint = α • 1
    ↔
  ∀ i, (ψ i).matrix⁻¹.trace = α :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply,
    linear_map.mul'_comp_mul'_adjoint_direct_sum, function.funext_iff,
    finset.sum_apply, pi.smul_apply, include_block_apply, dite_apply, pi.zero_apply,
    smul_dite, smul_zero, finset.sum_dite_eq', finset.mem_univ, if_true,
    linear_map.smul_apply, linear_map.one_apply, pi.smul_apply],
  simp only [eq_mp_eq_cast, cast_eq, ← pi.smul_apply],
  split,
  { intros h i,
    specialize h (1 : ℍ₂) i,
    rw [matrix.ext_iff, ← sub_eq_zero] at h,
    simp only [] at h,
    rw [← pi.sub_apply, ← sub_smul, pi.smul_apply, pi.one_apply, smul_eq_zero] at h,
    simp_rw [sub_eq_zero, one_ne_zero', or_false] at h,
    exact h, },
  { intros h i j k l,
    rw h, },
end

lemma linear_map.is_faithful_pos_map.direct_sum.inner_coord'
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (ij : (s i) × (s i)) (x : ℍ₂) :
  ⟪linear_map.is_faithful_pos_map.direct_sum.basis (λ i, (hψ i).elim) ⟨i, ij⟩, x⟫_ℂ
    = (x * (λ j, (hψ j).elim.matrix_is_pos_def.rpow (1 / 2))) i ij.1 ij.2 :=
begin
  simp_rw [linear_map.is_faithful_pos_map.direct_sum.basis_apply,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply,
    pi.mul_apply, linear_map.is_faithful_pos_map.include_block_left_inner,
    linear_map.is_faithful_pos_map.inner_coord],
  refl,
end

lemma linear_map.is_faithful_pos_map.direct_sum.map_star
  (hψ : Π i, (ψ i).is_faithful_pos_map) (x : ℍ₂) :
  linear_map.direct_sum ψ (star x) = star (linear_map.direct_sum ψ x) :=
linear_map.is_pos_map.direct_sum.is_real (λ i, (hψ i).1) x

lemma nontracial.direct_sum.unit_adjoint_eq [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  (algebra.linear_map ℂ ℍ₂ : ℂ →ₗ[ℂ] ℍ₂).adjoint = linear_map.direct_sum ψ :=
begin
  rw [← @linear_map.is_faithful_pos_map.direct_sum_adjoint_eq _ _ _ _ _ _ ψ,
    linear_map.adjoint_adjoint],
end

def linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def
  (hψ : Π i, fact (ψ i).is_faithful_pos_map) :=
λ i, (hψ i).elim.matrix_is_pos_def

noncomputable def pi.pos_def.rpow
  {a : ℍ₂} (ha : Π i, (a i).pos_def) (r : ℝ) :=
λ i, (ha i).rpow r

lemma pi.pos_def.rpow_mul_rpow
  {a : ℍ₂} (ha : Π i, (a i).pos_def) (r₁ r₂ : ℝ) :
  (pi.pos_def.rpow ha r₁)
    * (pi.pos_def.rpow ha r₂)
    = pi.pos_def.rpow ha (r₁ + r₂) :=
begin
  ext1 i,
  simp only [pi.mul_apply, pi.pos_def.rpow, mul_eq_mul, pos_def.rpow_mul_rpow],
end

lemma pi.pos_def.rpow_zero {a : ℍ₂} (ha : Π i, (a i).pos_def) :
  pi.pos_def.rpow ha 0 = 1 :=
begin
  ext1 i,
  simp only [pi.pos_def.rpow, pos_def.rpow_zero, pi.one_apply],
end

lemma linear_map.is_faithful_pos_map.include_block_right_inner
  {k : Type u_1}  [fintype k] [decidable_eq k]  {s : k → Type u_2}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  {ψ : Π (i : k), matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ} [hψ : ∀ (i : k), fact (ψ i).is_faithful_pos_map]
  {i : k} (y : Π (j : k), matrix (s j) (s j) ℂ) (x : matrix (s i) (s i) ℂ) :
  ⟪y, include_block x⟫_ℂ = ⟪y i, x⟫_ℂ :=
begin
  rw [← inner_conj_symm, linear_map.is_faithful_pos_map.include_block_left_inner,
    inner_conj_symm],
end

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y

lemma direct_sum_include_block_right_rank_one [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (a : ℍ₂) {i : k} (b : ℍ_ i) (c : ℍ₂) (j : k) :
  |a⟩⟨include_block b| c j =
    ⟪b, c i⟫_ℂ • a j :=
begin
  simp only [rank_one_apply, linear_map.is_faithful_pos_map.include_block_left_inner, pi.smul_apply],
end
lemma direct_sum_include_block_left_rank_one [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (b : ℍ₂) {i : k} (a : ℍ_ i) (c : ℍ₂) (j : k) :
  |include_block a⟩⟨b| c j =
    ⟪b, c⟫_ℂ • dite (i = j) (λ h, by rw ← h; exact a) (λ h, 0) :=
begin
  simp only [rank_one_apply, linear_map.is_faithful_pos_map.include_block_left_inner, pi.smul_apply,
    include_block_apply, smul_dite, smul_zero],
  refl,
end

noncomputable def linear_map.is_faithful_pos_map.direct_sum.sig
  (hψ : Π i, fact (ψ i).is_faithful_pos_map) (z : ℝ) :
  ℍ₂ ≃ₐ[ℂ] ℍ₂ :=
{ to_fun := λ x, pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) (-z)
  * x * pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) z,
  inv_fun := λ x, pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) (z)
  * x * pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) (-z),
  left_inv := λ x, by { simp only [← mul_assoc, pi.pos_def.rpow_mul_rpow],
    simp only [mul_assoc, pi.pos_def.rpow_mul_rpow],
    simp only [add_neg_self, pi.pos_def.rpow_zero, one_mul, mul_one, neg_add_self], },
  right_inv := λ x, by { simp only [← mul_assoc, pi.pos_def.rpow_mul_rpow],
    simp only [mul_assoc, pi.pos_def.rpow_mul_rpow],
    simp only [add_neg_self, pi.pos_def.rpow_zero, one_mul, mul_one, neg_add_self], },
  map_add' := λ x y, by { simp only [mul_add, add_mul], },
  commutes' := λ r, by { simp only [algebra.algebra_map_eq_smul_one, mul_smul_comm, smul_mul_assoc,
    mul_one, pi.pos_def.rpow_mul_rpow, neg_add_self, pi.pos_def.rpow_zero], },
  map_mul' := λ x y, by { simp_rw [mul_assoc],
    simp only [← mul_assoc (pi.pos_def.rpow _ z) (pi.pos_def.rpow _ (-z)) (y * _),
      pi.pos_def.rpow_mul_rpow, add_neg_self, pi.pos_def.rpow_zero, one_mul], } }

lemma linear_map.is_faithful_pos_map.direct_sum.sig_apply
  (hψ : Π i, fact (ψ i).is_faithful_pos_map) (z : ℝ) (x : ℍ₂) :
  linear_map.is_faithful_pos_map.direct_sum.sig hψ z x
    = pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) (-z)
  * x * pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) z :=
rfl

lemma linear_map.is_faithful_pos_map.direct_sum.sig_symm_apply
  (hψ : Π i, fact (ψ i).is_faithful_pos_map) (z : ℝ) (x : ℍ₂) :
  (linear_map.is_faithful_pos_map.direct_sum.sig hψ z).symm x
    = pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) z
  * x * pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def hψ) (-z) :=
rfl

lemma linear_map.is_faithful_pos_map.direct_sum.sig_symm_eq
  (hψ : Π i, fact (ψ i).is_faithful_pos_map) (z : ℝ) :
  (linear_map.is_faithful_pos_map.direct_sum.sig hψ z).symm
    = linear_map.is_faithful_pos_map.direct_sum.sig hψ (-z) :=
begin
  ext1,
  simp only [linear_map.is_faithful_pos_map.direct_sum.sig_apply,
    linear_map.is_faithful_pos_map.direct_sum.sig_symm_apply, neg_neg],
end

lemma pi.pos_def.rpow.is_pos_def {a : ℍ₂} (ha : Π i, (a i).pos_def) (r : ℝ) :
  Π i, ((pi.pos_def.rpow ha r) i).pos_def :=
begin
  intros i,
  simp only [pi.pos_def.rpow],
  exact pos_def.rpow.is_pos_def _ _,
end

end direct_sum
