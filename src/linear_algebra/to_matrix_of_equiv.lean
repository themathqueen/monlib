/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.basic
import linear_algebra.inner_aut
import linear_algebra.my_matrix.reshape

/-!

# to_matrix_of_equiv

This defines the identification $L(M_{n \times m})\cong_{a} M_{n \times m}$
  (see `linear_map.to_matrix_of_alg_equiv`; also see `matrix.to_lin_of_alg_equiv`).

-/

variables {R I J 𝕜 : Type*} [fintype I] [fintype J] [is_R_or_C 𝕜]
  [comm_semiring R] [decidable_eq I] [decidable_eq J]

open_locale big_operators
open matrix

/-- the star-algebraic isomorphism from `E →ₗ[𝕜] E` to the matrix ring `M_n(𝕜)` given by
  the orthonormal basis `b` on `E` -/
noncomputable def orthonormal_basis.to_matrix
  {n E : Type*} [fintype n] [decidable_eq n] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (b : orthonormal_basis n 𝕜 E) :
  (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] matrix n n 𝕜 :=
{ to_fun := λ x k p, inner (b k) (x (b p)),
  inv_fun := λ x, ∑ i j, x i j • (rank_one (b i) (b j) : E →L[𝕜] E),
  map_add' := λ x y, by { simp only [linear_map.add_apply, inner_add_right], refl, },
  map_smul' := λ r x, by { simp only [linear_map.smul_apply, inner_smul_right], refl, },
  map_mul' := λ x y, by { ext1, simp only [linear_map.mul_apply, mul_eq_mul, matrix.mul_apply,
    ← linear_map.adjoint_inner_left x, orthonormal_basis.sum_inner_mul_inner], },
  map_star' := λ x, by { ext1, simp only [star_eq_conj_transpose, conj_transpose_apply,
    linear_map.star_eq_adjoint, linear_map.adjoint_inner_right, is_R_or_C.star_def,
    inner_conj_symm], },
  right_inv := λ x, by { ext1,  simp only [linear_map.sum_apply, linear_map.smul_apply,
      continuous_linear_map.coe_coe, rank_one_apply, inner_sum, smul_smul, inner_smul_right],
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_boole, finset.sum_ite_irrel,
      finset.sum_const_zero, finset.sum_ite_eq, finset.sum_ite_eq', finset.mem_univ, if_true], },
  left_inv := λ x, by { ext1, simp only [linear_map.sum_apply, linear_map.smul_apply,
      continuous_linear_map.coe_coe, rank_one_apply, ← linear_map.adjoint_inner_left x,
      smul_smul, ← finset.sum_smul, orthonormal_basis.sum_inner_mul_inner],
    simp_rw [linear_map.adjoint_inner_left, ← orthonormal_basis.repr_apply_apply,
      orthonormal_basis.sum_repr], } }

lemma orthonormal_basis.to_matrix_apply
  {n E : Type*} [fintype n] [decidable_eq n] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (b : orthonormal_basis n 𝕜 E)
  (x : E →ₗ[𝕜] E) (i j : n) :
  b.to_matrix x i j = inner (b i) (x (b j)) :=
rfl

lemma orthonormal_basis.to_matrix_symm_apply
  {n E : Type*} [fintype n] [decidable_eq n] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (b : orthonormal_basis n 𝕜 E)
  (x : matrix n n 𝕜) :
  b.to_matrix.symm x = ∑ i j, x i j • (rank_one (b i) (b j) : E →L[𝕜] E) :=
rfl

lemma orthonormal_basis.to_matrix_symm_apply'
  {n E : Type*} [fintype n] [decidable_eq n] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (b : orthonormal_basis n 𝕜 E) (x : matrix n n 𝕜) :
  b.to_matrix.symm x = b.repr.symm.conj (mul_vec_lin x) :=
begin
  ext1 a,
  simp only [linear_equiv.conj_apply, linear_equiv.conj_apply_apply,
    linear_isometry_equiv.to_linear_equiv_symm, linear_isometry_equiv.symm_symm],
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe,
    linear_isometry_equiv.coe_to_linear_equiv, mul_vec_lin, linear_map.coe_mk,
    orthonormal_basis.to_matrix_symm_apply, linear_map.sum_apply, linear_map.smul_apply,
    continuous_linear_map.coe_coe, rank_one_apply, smul_smul, mul_comm (x _ _), ← smul_smul],
  rw finset.sum_comm,
  simp_rw [← finset.smul_sum, ← orthonormal_basis.repr_apply_apply],
  have : ∀ i j, x i j = x.mul_vec (b.repr (b j)) i,
  { simp_rw [mul_vec, dot_product, orthonormal_basis.repr_self,
      euclidean_space.single_apply, mul_boole, finset.sum_ite_eq',
      finset.mem_univ, if_true, eq_self_iff_true, forall_2_true_iff], },
  simp_rw [this, orthonormal_basis.sum_repr_symm, ← smul_hom_class.map_smul, ← mul_vec_smul_assoc,
    ← linear_isometry_equiv.map_smul, ← map_sum, ← mul_vec_sum, ← map_sum,
    orthonormal_basis.sum_repr],
end

lemma orthonormal_basis_to_matrix_eq_basis_to_matrix
  {n E : Type*} [fintype n] [decidable_eq n] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (b : orthonormal_basis n 𝕜 E) :
  linear_map.to_matrix_alg_equiv b.to_basis = b.to_matrix.to_alg_equiv :=
begin
  ext,
  simp_rw [star_alg_equiv.coe_to_alg_equiv, orthonormal_basis.to_matrix_apply,
    linear_map.to_matrix_alg_equiv_apply, orthonormal_basis.coe_to_basis_repr_apply,
    orthonormal_basis.repr_apply_apply, orthonormal_basis.coe_to_basis],
end


noncomputable def euclidean_space.orthonormal_basis (n 𝕜 : Type*) [is_R_or_C 𝕜] [fintype n] [decidable_eq n] :
  orthonormal_basis n 𝕜 (euclidean_space 𝕜 n) :=
begin
  refine basis.to_orthonormal_basis (pi.basis_fun 𝕜 n) _,
  rw [orthonormal_iff_ite],
  intros x y,
  simp_rw [inner, pi.basis_fun_apply, linear_map.coe_std_basis, pi.single,
    function.update_apply, star_ring_end_apply, star_ite, pi.zero_apply, star_one, star_zero,
    boole_mul, finset.sum_ite_eq', finset.mem_univ, if_true],
end

lemma euclidean_space.orthonormal_basis.repr_eq_one {n : Type*} [fintype n] [decidable_eq n] :
  (euclidean_space.orthonormal_basis n 𝕜 : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n)).repr = 1 :=
rfl

lemma linear_isometry_equiv.to_linear_equiv_one {R E : Type*}
  [_inst_1 : semiring R]  [_inst_25 : seminormed_add_comm_group E] [_inst_29 : module R E] :
  (1 : E ≃ₗᵢ[R] E).to_linear_equiv = 1 :=
rfl

lemma linear_equiv.one_symm {R E : Type*} [semiring R] [add_comm_monoid E] [module R E] :
  (1 : E ≃ₗ[R] E).symm = 1 :=
rfl

lemma linear_equiv.to_linear_map_one {R E : Type*} [semiring R] [add_comm_monoid E] [module R E] :
  (1 : E ≃ₗ[R] E).to_linear_map = 1 :=
rfl


lemma linear_equiv.refl_conj {R E : Type*} [comm_semiring R] [add_comm_monoid E] [module R E] :
  (linear_equiv.refl R E).conj = 1 :=
begin
  ext,
  simp only [linear_equiv.conj_apply_apply, linear_equiv.refl_apply,
    linear_equiv.refl_symm],
  refl,
end

lemma linear_equiv.conj_mul {R E F : Type*} [comm_semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R E] [module R F] (f : E ≃ₗ[R] F) (x y : module.End R E) :
  f.conj (x * y) = f.conj x * f.conj y :=
begin
  simp only [linear_map.mul_eq_comp, linear_equiv.conj_comp],
end

lemma linear_equiv.conj_apply_one {R E F : Type*} [comm_semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R E] [module R F] (f : E ≃ₗ[R] F) :
  f.conj 1 = 1 :=
linear_equiv.conj_id _

lemma linear_equiv.conj_one {R E : Type*} [comm_semiring R] [add_comm_monoid E] [module R E] :
  (1 : E ≃ₗ[R] E).conj = 1 :=
begin
  ext,
  simp only [linear_equiv.conj_apply, linear_map.comp_apply, linear_equiv.coe_coe],
  refl,
end

lemma linear_equiv.one_apply {R E : Type*} [comm_semiring R] [add_comm_monoid E]
  [module R E] (x : E) :
  (1 : E ≃ₗ[R] E) x = x :=
rfl


lemma orthonormal_basis.std_to_matrix {n : Type*} [fintype n] [decidable_eq n] :
  (@orthonormal_basis.to_matrix 𝕜 _ _ _ _ _ _ _ (@euclidean_space.finite_dimensional n 𝕜 _ _)
    (euclidean_space.orthonormal_basis n 𝕜 :
      orthonormal_basis n 𝕜 (euclidean_space 𝕜 n))).symm.to_alg_equiv.to_linear_equiv
  = to_euclidean_lin :=
begin
  ext1,
  rw [alg_equiv.to_linear_equiv_apply, star_alg_equiv.coe_to_alg_equiv,
    orthonormal_basis.to_matrix_symm_apply', euclidean_space.orthonormal_basis.repr_eq_one,
    ← linear_isometry_equiv.to_linear_equiv_symm, linear_isometry_equiv.to_linear_equiv_one,
    linear_equiv.one_symm, linear_equiv.conj_one, linear_equiv.one_apply],
  refl,
end

lemma matrix.std_basis_repr_eq_reshape :
  (matrix.std_basis R I J).equiv_fun = reshape  :=
begin
  ext x ij,
  simp_rw [basis.equiv_fun_apply],
  rw [basis.repr_apply_eq],
  { intros x y,
    simp_rw [map_add], },
  { intros c x,
    simp_rw [smul_hom_class.map_smul], },
  { intros i,
    ext1,
    simp_rw [reshape_apply, matrix.std_basis, basis.reindex_apply, pi.basis_apply],
    simp only [pi.basis_fun_apply, linear_map.std_basis_apply, function.update_apply,
      pi.zero_apply],
    simp only [ite_apply, pi.zero_apply, function.update_apply, finsupp.single_apply,
      ← ite_and, @eq_comm _ i x_1, equiv.sigma_equiv_prod_symm_apply],
    congr',
    nth_rewrite_lhs 0 ← prod.eq_iff_fst_eq_snd_eq, },
end

namespace linear_map

open_locale matrix complex_conjugate big_operators

open is_R_or_C matrix

lemma to_matrix_std_basis_std_basis {I J K L : Type*} [fintype I] [fintype J]
  [fintype K] [fintype L] [decidable_eq I] [decidable_eq J]
  (x : matrix I J R →ₗ[R] matrix K L R) :
  to_matrix (matrix.std_basis R I J) (matrix.std_basis R K L) x
    = ((reshape : matrix K L R ≃ₗ[R] _).to_linear_map ∘ₗ x
      ∘ₗ (reshape : matrix I J R ≃ₗ[R] _).symm.to_linear_map).to_matrix' :=
rfl

lemma to_lin_std_basis_std_basis {I J K L : Type*} [fintype I] [fintype J]
  [fintype K] [fintype L] [decidable_eq I] [decidable_eq J]
  (x : matrix (K × L) (I × J) R) :
  (to_lin (matrix.std_basis R I J) (matrix.std_basis R K L)) x
    = (reshape : matrix K L R ≃ₗ[R] _).symm.to_linear_map ∘ₗ x.to_lin'
      ∘ₗ (reshape : matrix I J R ≃ₗ[R] _).to_linear_map :=
rfl

def linear_equiv.inner_conj {R E F : Type*} [comm_semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R E] [module R F] (ϱ : E ≃ₗ[R] F) :
  (E →ₗ[R] E) ≃ₐ[R] (F →ₗ[R] F) :=
begin
  apply alg_equiv.of_linear_equiv ϱ.conj (linear_equiv.conj_mul _),
  intros r,
  simp only [algebra.algebra_map_eq_smul_one, smul_hom_class.map_smul,
    linear_equiv.conj_apply_one],
end

def to_matrix_of_alg_equiv :
  (matrix I J R →ₗ[R] matrix I J R) ≃ₐ[R] matrix (I × J) (I × J) R :=
(reshape : matrix I J R ≃ₗ[R] _).inner_conj.trans to_matrix_alg_equiv'

lemma to_matrix_of_alg_equiv_apply (x : matrix I J R →ₗ[R] matrix I J R) :
  x.to_matrix_of_alg_equiv = ((reshape : matrix I J R ≃ₗ[R] _).to_linear_map
      ∘ₗ x ∘ₗ (reshape : matrix I J R ≃ₗ[R] _).symm.to_linear_map).to_matrix_alg_equiv' :=
rfl

lemma to_matrix_of_alg_equiv_symm_apply (x : matrix (I × J) (I × J) R) :
  to_matrix_of_alg_equiv.symm x = (reshape : matrix I J R ≃ₗ[R] _).symm.to_linear_map
    ∘ₗ (to_matrix_alg_equiv'.symm x) ∘ₗ (reshape : matrix I J R ≃ₗ[R] _).to_linear_map :=
rfl

lemma to_matrix_of_alg_equiv_apply' (x : matrix I J R →ₗ[R] matrix I J R) (ij kl : I × J) :
  x.to_matrix_of_alg_equiv ij kl = x (std_basis_matrix kl.1 kl.2 (1 : R)) ij.1 ij.2 :=
begin
  simp_rw [to_matrix_of_alg_equiv_apply, to_matrix_alg_equiv'_apply, linear_map.comp_apply,
    linear_equiv.to_linear_map_eq_coe, linear_equiv.coe_coe, reshape_apply, std_basis_matrix,
    ← prod.mk.inj_iff, prod.mk.eta, eq_comm],
  refl,
end

end linear_map

namespace matrix

def to_lin_of_alg_equiv :
  matrix (I × J) (I × J) R ≃ₐ[R] (matrix I J R →ₗ[R] matrix I J R) :=
linear_map.to_matrix_of_alg_equiv.symm

lemma to_lin_of_alg_equiv_apply (x : matrix (I × J) (I × J) R) (y : matrix I J R) :
  x.to_lin_of_alg_equiv y = (reshape : matrix I J R ≃ₗ[R] (I × J → R)).symm
    (x.to_lin_alg_equiv' (reshape y)) :=
rfl

def rank_one_std_basis (ij kl : I × J) (r : R) :
  matrix I J R →ₗ[R] matrix I J R :=
{ to_fun := λ x, std_basis_matrix ij.1 ij.2 (r • r • (x kl.1 kl.2)),
  map_add' := λ x y, by { simp_rw [pi.add_apply, smul_add,
    std_basis_matrix_add], },
  map_smul' := λ r x, by { simp_rw [ring_hom.id_apply, pi.smul_apply,
    smul_std_basis_matrix, smul_smul, mul_rotate'], } }

lemma rank_one_std_basis_apply (ij kl : I × J) (r : R) (x : matrix I J R) :
  rank_one_std_basis ij kl r x = std_basis_matrix ij.1 ij.2 (r • r • (x kl.1 kl.2)) :=
rfl

open_locale big_operators

lemma to_lin_of_alg_equiv_eq (x : matrix (I × J) (I × J) R) :
  x.to_lin_of_alg_equiv = ∑ (ij kl : I × J), x ij kl
    • rank_one_std_basis ij kl (1 : R) :=
begin
  simp_rw [linear_map.ext_iff, ← ext_iff, to_lin_of_alg_equiv_apply, reshape_symm_apply,
    linear_map.sum_apply, finset.sum_apply, to_lin_alg_equiv'_apply, mul_vec, dot_product,
    reshape_apply, linear_map.smul_apply, pi.smul_apply, rank_one_std_basis_apply,
    std_basis_matrix, smul_ite, ← prod.mk.inj_iff, prod.mk.eta, one_smul,
    smul_zero, smul_eq_mul, finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq',
    finset.mem_univ, if_true, eq_self_iff_true, forall_3_true_iff],
end

-- MOVE:
lemma to_lin_of_alg_equiv_to_matrix_of_alg_equiv (x : matrix (I × J) (I × J) R) :
  x.to_lin_of_alg_equiv.to_matrix_of_alg_equiv = x :=
by rw [to_lin_of_alg_equiv, alg_equiv.apply_symm_apply]


end matrix

open matrix

variables {n : Type*} [fintype n] [decidable_eq n]

-- MOVE:
lemma linear_map.to_matrix_of_alg_equiv_to_lin_of_alg_equiv
  (x : matrix I J R →ₗ[R] matrix I J R) :
  x.to_matrix_of_alg_equiv.to_lin_of_alg_equiv = x :=
by rw [to_lin_of_alg_equiv, alg_equiv.symm_apply_apply]

open_locale kronecker matrix
lemma inner_aut_coord (U : unitary_group n 𝕜) :
  (inner_aut U).to_matrix_of_alg_equiv = U ⊗ₖ Uᴴᵀ :=
begin
  ext1,
  simp_rw [linear_map.to_matrix_of_alg_equiv_apply', inner_aut_apply',
    mul_apply, std_basis_matrix, mul_ite, mul_one, mul_zero, finset.sum_mul, ite_mul, zero_mul,
    ite_and, ← unitary_group.star_coe_eq_coe_star, star_apply, kronecker_map_apply, conj_apply],
  simp only [finset.sum_ite_eq, finset.mem_univ, if_true],
end

lemma matrix.inner_aut_coord (U : unitary_group n 𝕜) (ij kl : n × n) :
  (inner_aut U).to_matrix_of_alg_equiv ij kl = (U ij.1 kl.1) * star (U ij.2 kl.2) :=
begin
  rw inner_aut_coord, refl,
end

lemma inner_aut_inv_coord (U : unitary_group n ℂ) (ij kl : n × n) :
  (inner_aut U⁻¹).to_matrix_of_alg_equiv ij kl = (U kl.2 ij.2) * star (U kl.1 ij.1) :=
begin
  simp_rw [inner_aut_coord, unitary_group.inv_apply, star_eq_conj_transpose,
    kronecker_map_apply, conj_apply, conj_transpose_apply, star_star, mul_comm],
end
