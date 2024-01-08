/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.spectrum
import linear_algebra.my_matrix.conj
import linear_algebra.trace
import preq.finset
import linear_algebra.my_ips.rank_one
import data.matrix.kronecker

/-!

# Some obvious lemmas on matrices

This file includes some necessary and obvious results for matrices,
such as `matrix.mul_vec_eq`.

We also show that the trace of a symmetric matrix is equal to the sum of its eigenvalues.

-/

namespace matrix

variables {𝕜 n : Type*} [field 𝕜] [fintype n]

lemma eq_zero {R n₁ n₂ : Type*} [has_zero R] (x : matrix n₁ n₂ R) :
  (∀ (i : n₁) (j : n₂), x i j = 0) ↔ x = 0 :=
by simp_rw [← matrix.ext_iff, pi.zero_apply]

/-- two matrices $a,b \in M_n$ are equal iff for all vectors $c \in \mathbb{k}^n$ we have $a c = b c$,
  essentially, treat them as linear maps on $\mathbb{k}^n$ so you can have extentionality with vectors -/
lemma mul_vec_eq {R m n : Type*} [comm_semiring R] [fintype n] [decidable_eq n]
  (a b : matrix m n R) :
  a = b ↔ ∀ (c : n → R), a.mul_vec c = b.mul_vec c :=
begin
  refine ⟨λ h c, by rw h, λ h, _⟩,
  ext,
  rw [← mul_vec_std_basis a i j, ← mul_vec_std_basis b i j, h _],
end

/-- a vector is nonzero iff one of its elements are nonzero -/
lemma vec_ne_zero {R n : Type*} [semiring R] (a : n → R) :
  (∃ i, a i ≠ 0) ↔ a ≠ 0 :=
begin
  simp_rw [ne.def, ← not_forall],
  split,
  { intros h h2,
    simp_rw [h2, pi.zero_apply, eq_self_iff_true, implies_true_iff, not_true] at h,
    exact h, },
  { intros h h2,
    apply h,
    ext,
    rw pi.zero_apply,
    exact h2 x, },
end

/-- two vectors are equal iff their elements are equal -/
lemma ext_vec (α β : n → 𝕜) : α = β ↔ ∀ i : n, α i = β i :=
begin
  refine ⟨λ h i, by rw h, λ h, _⟩,
  ext i, exact h i,
end

/-- the outer product of two nonzero vectors is nonzero -/
lemma vec_mul_vec_ne_zero {R n : Type*} [semiring R] [no_zero_divisors R]
  {α β : n → R} (hα : α ≠ 0) (hβ : β ≠ 0) :
  vec_mul_vec α β ≠ 0 :=
begin
  rw [ne.def, ← ext_iff],
  rw ← vec_ne_zero at hα hβ,
  cases hβ with i hiy,
  cases hα with j hju,
  simp_rw [vec_mul_vec_eq, mul_apply, fintype.univ_punit, col_apply, row_apply,
    finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one,
    one_mul, pi.zero_apply, mul_eq_zero, not_forall],
  use j, use i,
  push_neg,
  exact ⟨hju, hiy⟩,
end

/--  the transpose of `vec_mul_vec x y` is simply `vec_mul_vec y x`  -/
lemma vec_mul_vec_transpose {R n : Type*} [comm_semiring R]
  (x y : n → R) :
  (vec_mul_vec x y).transpose = vec_mul_vec y x :=
begin
  simp_rw [← matrix.ext_iff, transpose_apply, vec_mul_vec, mul_comm,
    of_apply, eq_self_iff_true, forall_2_true_iff],
end

open_locale big_operators

/-- the identity written as a sum of the standard basis -/
lemma one_eq_sum_std_matrix {n R : Type*} [comm_semiring R] [fintype n]
  [decidable_eq n] :
  (1 : matrix n n R) = ∑ (r : n), matrix.std_basis_matrix r r (1 : R) :=
by simp_rw [← matrix.ext_iff, finset.sum_apply, matrix.one_apply,
  matrix.std_basis_matrix, ite_and, finset.sum_ite_eq', finset.mem_univ,
  if_true, eq_self_iff_true, forall_2_true_iff]

open_locale matrix complex_conjugate

open is_R_or_C matrix

end matrix

section trace

variables {ℍ ℍ₂ 𝕜 : Type*} [normed_add_comm_group ℍ]
  [normed_add_comm_group ℍ₂] [is_R_or_C 𝕜]
  [inner_product_space 𝕜 ℍ] [inner_product_space 𝕜 ℍ₂]
  [finite_dimensional 𝕜 ℍ] [finite_dimensional 𝕜 ℍ₂]
  {n : Type*} [fintype n]

local notation `l(`x`)` := x →ₗ[𝕜] x
local notation `L(`x`)` := x →L[𝕜] x
local notation `𝕂` x := matrix x x 𝕜

open_locale tensor_product kronecker big_operators

/-- $\textnormal{Tr}(A\otimes_k B)=\textnormal{Tr}(A)\textnormal{Tr}(B)$ -/
lemma matrix.kronecker.trace (A B : 𝕂 n) :
  (A ⊗ₖ B).trace = A.trace * B.trace :=
begin
  simp_rw [matrix.trace, matrix.diag, matrix.kronecker_map, finset.sum_mul_sum],
  refl,
end

example (A : l(ℍ)) (B : l(ℍ₂)) :
  linear_map.trace 𝕜 (ℍ ⊗[𝕜] ℍ₂) (tensor_product.map A B)
    = linear_map.trace 𝕜 ℍ A * linear_map.trace 𝕜 ℍ₂ B :=
linear_map.trace_tensor_product' _ _

open linear_map

/-- the trace of a Hermitian matrix is the sum of its eigenvalues -/
lemma matrix.is_hermitian.trace_eq [decidable_eq n] [decidable_eq 𝕜]
  {A : 𝕂 n} (hA : A.is_hermitian) :
  A.trace = ∑ (i : n), hA.eigenvalues i :=
begin
  simp_rw [hA.eigenvalues_eq, matrix.trace, matrix.diag, matrix.dot_product,
    pi.star_apply, matrix.mul_vec, matrix.transpose_apply, matrix.dot_product,
    matrix.transpose_apply, matrix.is_hermitian.eigenvector_matrix_apply,
    ← hA.eigenvector_matrix_inv_apply, finset.mul_sum,
    ← hA.eigenvector_matrix_apply, mul_comm _ (_ * _), mul_assoc,
    _root_.map_sum],
  norm_cast,
  rw finset.sum_comm,
  have := calc ∑ (y : n) (x : n) (i : n),
    is_R_or_C.re (A y i * (hA.eigenvector_matrix i x * hA.eigenvector_matrix_inv x y))
        = ∑ (i y : n), is_R_or_C.re (A y i
    * (∑ (x : n), hA.eigenvector_matrix i x * hA.eigenvector_matrix_inv x y)) :
    by { simp_rw [finset.mul_sum, _root_.map_sum], rw finset.sum_sum_sum, }
    ... = ∑ (i y : n), is_R_or_C.re (A y i * (1 : 𝕂 n) i y) :
    by { simp_rw [← matrix.mul_apply, matrix.is_hermitian.eigenvector_matrix_mul_inv], }
    ... = ∑ (y : n), is_R_or_C.re (∑ (i : n), A y i * (1 : 𝕂 n) i y) :
    by { simp_rw [← _root_.map_sum], rw finset.sum_comm }
    ... = ∑ (y : n), is_R_or_C.re ((A.mul 1) y y) : by simp_rw ← matrix.mul_apply
    ... = ∑ (y : n), is_R_or_C.re (A y y) : by rw matrix.mul_one,
  { rw [this, is_R_or_C.of_real_sum],
    congr,
    ext1 i,
    rw [hA.coe_re_apply_self i], },
end

lemma linear_map.is_symmetric.eigenvalue_mem_spectrum [decidable_eq 𝕜]
  (hn : finite_dimensional.finrank 𝕜 ℍ = fintype.card n)
  {A : l(ℍ)} (hA : A.is_symmetric) (i : (fin (fintype.card n))) :
  (hA.eigenvalues hn i : 𝕜) ∈ spectrum 𝕜 A :=
begin
  simp_rw ← module.End.has_eigenvalue_iff_mem_spectrum,
  exact hA.has_eigenvalue_eigenvalues hn i,
end

lemma matrix.is_hermitian.eigenvalues_has_eigenvalue
  {𝕜 n : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  [decidable_eq 𝕜] {M : matrix n n 𝕜} (hM : M.is_hermitian) (i : n) :
  module.End.has_eigenvalue M.to_euclidean_lin (hM.eigenvalues i) :=
begin
  simp_rw [matrix.is_hermitian.eigenvalues, matrix.is_hermitian.eigenvalues₀],
  exact linear_map.is_symmetric.has_eigenvalue_eigenvalues _ _ _,
end

lemma matrix.is_hermitian.has_eigenvector_eigenvector_basis
  {𝕜 n : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  [decidable_eq 𝕜] {M : matrix n n 𝕜} (hM : M.is_hermitian) (i : n) :
  module.End.has_eigenvector M.to_euclidean_lin (hM.eigenvalues i) (hM.eigenvector_basis i) :=
begin
  simp_rw [matrix.is_hermitian.eigenvector_basis, matrix.is_hermitian.eigenvalues,
    matrix.is_hermitian.eigenvalues₀, orthonormal_basis.reindex_apply],
  exact linear_map.is_symmetric.has_eigenvector_eigenvector_basis _ _ _,
end

/-- a Hermitian matrix applied to its eigenvector basis element equals
  the basis element scalar-ed by its respective eigenvalue -/
lemma matrix.is_hermitian.apply_eigenvector_basis {𝕜 n : Type*}
  [is_R_or_C 𝕜] [fintype n] [decidable_eq n] [decidable_eq 𝕜]
  {M : matrix n n 𝕜} (hM : M.is_hermitian) (i : n) :
  M.mul_vec (hM.eigenvector_basis i) = (hM.eigenvalues i) • (hM.eigenvector_basis i) :=
begin
  calc M.mul_vec (hM.eigenvector_basis i) = M.to_euclidean_lin (hM.eigenvector_basis i) : rfl
    ... = (hM.eigenvalues i) • (hM.eigenvector_basis i) : _,
  rw module.End.mem_eigenspace_iff.mp (hM.has_eigenvector_eigenvector_basis i).1,
  unfold_coes,
  simp only [ring_hom.to_fun_eq_coe, algebra_map_smul],
end

open_locale matrix

lemma euclidean_space.inner_eq {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n]
  {x y : n → 𝕜} :
  (@euclidean_space.inner_product_space n 𝕜 _ _).inner x y = star x ⬝ᵥ y :=
rfl

lemma euclidean_space.rank_one_of_orthonormal_basis_eq_one
  {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n]
  (h : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n)) :
  ∑ i : n, (rank_one (h i) (h i) : (euclidean_space 𝕜 n) →L[𝕜] (euclidean_space 𝕜 n)) = 1 :=
begin
  rw continuous_linear_map.ext_iff,
  intros x,
  apply @ext_inner_left 𝕜 _ _ _ euclidean_space.inner_product_space,
  intros v,
  simp_rw [continuous_linear_map.sum_apply, rank_one_apply],
  rw inner_sum,
  simp_rw [inner_smul_right, mul_comm, orthonormal_basis.sum_inner_mul_inner,
    continuous_linear_map.one_apply],
end

/-- for any matrix $x\in M_{n_1 \times n_2}$, we have
  $$x=\sum_{i,j,k,l}x_{ik}^{jl}(e_{ij} \otimes_k e_{kl}) $$ -/
lemma kmul_representation {R n₁ n₂ : Type*} [fintype n₁] [fintype n₂]
  [decidable_eq n₁] [decidable_eq n₂]
  [semiring R] (x : matrix (n₁ × n₂) (n₁ × n₂) R) :
  x = ∑ (i j : n₁) (k l : n₂), x (i,k) (j,l) • (matrix.std_basis_matrix i j (1 : R) ⊗ₖ matrix.std_basis_matrix k l (1 : R)) :=
begin
  simp_rw [← matrix.ext_iff, finset.sum_apply, pi.smul_apply, matrix.kronecker_map,
    matrix.std_basis_matrix, ite_mul, zero_mul, one_mul, matrix.of_apply,
    smul_ite, smul_zero, ite_and, finset.sum_ite_irrel, finset.sum_const_zero,
    finset.sum_ite_eq', finset.mem_univ, if_true, prod.mk.eta, smul_eq_mul,
    mul_one, eq_self_iff_true, forall_2_true_iff],
end

open matrix

/-- $(x \otimes_k y)^* = x^* \otimes_k y^*$ -/
lemma matrix.kronecker_conj_transpose {R m n : Type*} [comm_semiring R] [star_ring R]
  (x : matrix n n R) (y : matrix m m R) :
  (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ :=
begin
  simp_rw [← matrix.ext_iff, conj_transpose_apply, kronecker_map, of_apply, star_mul',
    conj_transpose_apply, eq_self_iff_true, forall_2_true_iff],
end

lemma matrix.kronecker.star (x y : matrix n n 𝕜) :
  star (x ⊗ₖ y) = (star x) ⊗ₖ (star y) :=
matrix.kronecker_conj_transpose _ _

-- MOVE:
lemma matrix.kronecker.transpose (x y : matrix n n 𝕜) :
  (x ⊗ₖ y)ᵀ = xᵀ ⊗ₖ yᵀ :=
begin
  simp_rw [← matrix.ext_iff],
  intros,
  simp only [matrix.transpose_apply, matrix.kronecker_map, of_apply],
end

lemma matrix.kronecker.conj (x y : matrix n n 𝕜) :
  (x ⊗ₖ y)ᴴᵀ = xᴴᵀ ⊗ₖ yᴴᵀ :=
by rw [conj, matrix.kronecker_conj_transpose, matrix.kronecker.transpose]; refl

lemma matrix.is_hermitian.eigenvector_matrix_mem_unitary_group {𝕜 : Type*}
  [is_R_or_C 𝕜] [decidable_eq 𝕜] [decidable_eq n]
  {x : matrix n n 𝕜} (hx : x.is_hermitian) :
  hx.eigenvector_matrix ∈ matrix.unitary_group n 𝕜 :=
begin
  simp_rw [mem_unitary_group_iff, star_eq_conj_transpose
  , mul_eq_mul,
    is_hermitian.conj_transpose_eigenvector_matrix, is_hermitian.eigenvector_matrix_mul_inv],
end

lemma matrix.unitary_group.coe_mk [decidable_eq n]
  (x : matrix n n 𝕜) (hx : x ∈ matrix.unitary_group n 𝕜) :
  ⇑(⟨x, hx⟩ : matrix.unitary_group n 𝕜) = x :=
rfl

end trace


open_locale matrix

variables {R n m : Type*} [semiring R] [star_add_monoid R]
  [decidable_eq n] [decidable_eq m]

@[simp] lemma matrix.std_basis_matrix_conj_transpose (i : n) (j : m) (a : R) :
  (matrix.std_basis_matrix i j a)ᴴ = matrix.std_basis_matrix j i (star a) :=
begin
  simp_rw [matrix.std_basis_matrix, ite_and],
  ext1 x, ext1 y,
  by_cases j = x ∧ i = y,
  { simp_rw [h.1, h.2, eq_self_iff_true, if_true, matrix.conj_transpose_apply,
      eq_self_iff_true, if_true], },
  simp_rw [matrix.conj_transpose_apply],
  by_cases h' : a = 0,
  { simp_rw [h', if_t_t, star_zero, if_t_t], },
  { simp_rw [← ite_and, and_comm _ (j = x), (ne.ite_eq_right_iff (star_ne_zero.mpr h')).mpr h,
      star_eq_iff_star_eq, star_zero],
    symmetry,
    rw ite_eq_right_iff,
    intros H,
    exfalso,
    exact h H, },
end

@[simp] lemma matrix.std_basis_matrix.star_apply (i k : n) (j l : m) (a : R) :
  star (matrix.std_basis_matrix i j a k l) = matrix.std_basis_matrix j i (star a) l k :=
begin
  rw [← matrix.std_basis_matrix_conj_transpose, ← matrix.conj_transpose_apply],
end

@[simp] lemma matrix.std_basis_matrix.star_apply' (i : n) (j : m) (x : n × m) (a : R) :
  star (matrix.std_basis_matrix i j a x.fst x.snd)
    = matrix.std_basis_matrix j i (star a) x.snd x.fst :=
by rw matrix.std_basis_matrix.star_apply

/-- $e_{ij}^*=e_{ji}$ -/
@[simp] lemma matrix.std_basis_matrix.star_one {R : Type*} [semiring R]
  [star_ring R] (i : n) (j : m) :
  (matrix.std_basis_matrix i j (1 : R))ᴴ = matrix.std_basis_matrix j i (1 : R) :=
begin
  nth_rewrite 1 ← star_one R,
  exact matrix.std_basis_matrix_conj_transpose _ _ _,
end

open_locale big_operators
@[simp] lemma matrix.trace_iff {R n : Type*} [add_comm_monoid R] [fintype n] (x : matrix n n R) :
  x.trace = ∑ k : n, (x k k) :=
rfl

@[simp] lemma matrix.std_basis_matrix.mul_apply_basis {R p q : Type*} [semiring R]
  [decidable_eq p] [decidable_eq q] (i x : n) (j y : m) (k z : p) (l w : q) :
  matrix.std_basis_matrix k l (matrix.std_basis_matrix i j (1 : R) x y) z w
    = (matrix.std_basis_matrix i j (1 : R) x y) * (matrix.std_basis_matrix k l (1 : R) z w) :=
begin
  simp_rw [matrix.std_basis_matrix, ite_and, ite_mul, zero_mul, one_mul, ← ite_and,
    and_rotate, and_assoc, and_comm],
end

@[simp] lemma matrix.std_basis_matrix.mul_apply_basis' {R p q : Type*} [semiring R]
  [decidable_eq p] [decidable_eq q] (i x : n) (j y : m) (k z : p) (l w : q) :
  matrix.std_basis_matrix k l (matrix.std_basis_matrix i j (1 : R) x y) z w
    = ite (i = x ∧ j = y ∧ k = z ∧ l = w) 1 0 :=
begin
  simp_rw [matrix.std_basis_matrix.mul_apply_basis, matrix.std_basis_matrix, ite_and, ite_mul,
           zero_mul, one_mul],
end

@[simp] lemma matrix.std_basis_matrix.mul_apply {R : Type*} [fintype n] [semiring R]
  (i j k l m p : n) :
  ∑ (x x_1 : n × n) (x_2 x_3 : n),
    matrix.std_basis_matrix l k (matrix.std_basis_matrix p m (1 : R) x_1.snd x_1.fst) x.snd x.fst
      * matrix.std_basis_matrix i x_2 (matrix.std_basis_matrix x_3 j (1 : R) x_1.fst x_1.snd) x.fst x.snd
  = ∑ (x x_1 : n × n) (x_2 x_3 : n),
    ite (p = x_1.snd ∧ m = x_1.fst ∧ l = x.snd ∧ k = x.fst ∧
         x_3 = x_1.fst ∧ j = x_1.snd ∧ i = x.fst ∧ x_2 = x.snd) 1 0 :=
begin
  simp_rw [matrix.std_basis_matrix.mul_apply_basis', ite_mul, one_mul, zero_mul,
    ← ite_and, and_assoc],
end

@[simp] lemma matrix.std_basis_matrix.sum_star_mul_self [fintype n] (i j : n) (a b : R) :
  ∑ k l m p : n, (matrix.std_basis_matrix i j a k l)
    * star (matrix.std_basis_matrix i j b) m p = a * star b :=
begin
  simp_rw [matrix.star_apply, matrix.std_basis_matrix.star_apply, matrix.std_basis_matrix, ite_mul,
    zero_mul, mul_ite, mul_zero, ite_and, finset.sum_ite_irrel, finset.sum_const_zero,
    finset.sum_ite_eq, finset.mem_univ, if_true],
end

lemma matrix.std_basis_matrix.sum_star_mul_self' {R : Type*} [fintype n]
  [semiring R] [star_ring R] (i j : n) :
  ∑ kl mp : n × n, (matrix.std_basis_matrix i j (1 : R) kl.1 kl.2) * (star matrix.std_basis_matrix i j (1 : R) mp.1 mp.2) = 1 :=
begin
  nth_rewrite_rhs 0 ← one_mul (1 : R),
  nth_rewrite_rhs 1 ← star_one R,
  nth_rewrite_rhs 0 ← matrix.std_basis_matrix.sum_star_mul_self i j _ _,
  simp_rw [← finset.mul_sum, ← finset.sum_product'],
  refl,
end

@[simp] lemma matrix.std_basis_matrix.mul_std_basis_matrix
  {R p : Type*} [semiring R] [decidable_eq p] [fintype m]
  (i x : n) (j k : m) (l y : p) (a b : R) :
  ((matrix.std_basis_matrix i j a) ⬝ (matrix.std_basis_matrix k l b)) x y =
    ite (i = x ∧ j = k ∧ l = y) (a * b) 0 :=
begin
  simp_rw [matrix.mul_apply, matrix.std_basis_matrix, ite_and, ite_mul, zero_mul,
    mul_ite, mul_zero, finset.sum_ite_irrel, finset.sum_ite_eq, finset.mem_univ, if_true,
    finset.sum_const_zero, eq_comm],
end

@[simp] lemma matrix.std_basis_matrix.mul_std_basis_matrix' {R p : Type*}
  [fintype n] [decidable_eq p] [semiring R]
  (i : m) (j k : n) (l : p) :
  matrix.std_basis_matrix i j (1 : R) ⬝ matrix.std_basis_matrix k l (1 : R)
    = (ite (j = k) (1 : R) 0) • matrix.std_basis_matrix i l (1 : R) :=
begin
  ext1 x y,
  simp_rw [pi.smul_apply, matrix.mul_apply, matrix.std_basis_matrix, ite_and, ite_mul, zero_mul,
    one_mul, finset.sum_ite_irrel, finset.sum_ite_eq, finset.mem_univ, if_true,
    finset.sum_const_zero, smul_ite, smul_zero, smul_eq_mul, mul_one, ← ite_and,
    eq_comm, and_comm],
end

lemma linear_map.to_matrix'_mul_vec {n R : Type*} [fintype n] [comm_semiring R] [decidable_eq n]
  (x : (n → R) →ₗ[R] n → R) (y : n → R) :
  x.to_matrix'.mul_vec y = x y :=
begin
  rw [← matrix.to_lin'_apply, matrix.to_lin'_to_matrix'],
end

def linear_equiv.to_invertible_matrix {n R : Type*} [comm_semiring R]
  [fintype n] [decidable_eq n] (x : (n → R) ≃ₗ[R] n → R) :
  invertible (x : (n → R) →ₗ[R] n → R).to_matrix' :=
begin
  refine invertible.mk (x.symm : (n → R) →ₗ[R] n → R).to_matrix' _ _;
  simp only [matrix.mul_eq_mul, ← linear_map.to_matrix'_mul, linear_map.mul_eq_comp,
    linear_equiv.comp_coe, linear_equiv.self_trans_symm, linear_equiv.symm_trans_self,
    linear_equiv.refl_to_linear_map, linear_map.to_matrix'_id],
end

lemma matrix.transpose_alg_equiv_symm_op_apply {n R α : Type*} [comm_semiring R] [comm_semiring α]
  [fintype n] [decidable_eq n] [algebra R α] (x : matrix n n α) :
  (matrix.transpose_alg_equiv n R α).symm (mul_opposite.op x) = xᵀ :=
by { simp_rw [matrix.transpose_alg_equiv_symm_apply, add_equiv.neg_fun_eq_symm, add_equiv.symm_trans_apply, matrix.transpose_add_equiv_symm, mul_opposite.op_add_equiv_symm_apply,
  mul_opposite.unop_op, matrix.transpose_add_equiv_apply], }

open matrix
lemma matrix.dot_product_eq_trace {R n : Type*} [comm_semiring R] [star_ring R] [fintype n]
  (x : n → R) (y : matrix n n R) :
  star x ⬝ᵥ (y.mul_vec x) = ((matrix.col x ⬝ matrix.row (star x))ᴴ ⬝ y).trace :=
begin
  simp_rw [trace_iff, dot_product, conj_transpose_mul, conj_transpose_row,
    conj_transpose_col, star_star, mul_apply, mul_vec, dot_product, col_apply, row_apply,
    pi.star_apply, fintype.univ_punit, finset.sum_const, finset.card_singleton,
    nsmul_eq_mul, algebra_map.coe_one, one_mul, finset.mul_sum, mul_comm (x _), mul_comm _ (x _),
    ← mul_assoc, mul_comm],
  rw finset.sum_comm,
end

lemma forall_left_mul {n R : Type*}
  [fintype n] [decidable_eq n] [semiring R] (x y : matrix n n R) :
  x = y ↔ ∀ a : matrix n n R, a * x = a * y :=
begin
  refine ⟨λ h a, by rw h, λ h, _⟩,
  specialize h 1,
  simp_rw one_mul at h,
  exact h,
end
