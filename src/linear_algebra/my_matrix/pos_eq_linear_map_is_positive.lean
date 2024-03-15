/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.matrix.pos_def
import linear_algebra.my_ips.pos
import linear_algebra.my_matrix.basic
import linear_algebra.End
import linear_algebra.my_ips.rank_one
import linear_algebra.matrix.nonsingular_inverse
import preq.ites
import preq.is_R_or_C_le

/-!

# the correspondence between matrix.pos_semidef and linear_map.is_positive

In this file, we show that
`x ∈ Mₙ` being positive semi-definite is equivalent to
`x.to_euclidean_lin.is_positive`

-/

-------------------------------
--copied from old mathlib
namespace matrix
 variables {𝕜 m n : Type*} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n] [is_R_or_C 𝕜]
 open_locale complex_conjugate

 /-- The adjoint of the linear map associated to a matrix is the linear map associated to the
 conjugate transpose of that matrix. -/
 lemma conj_transpose_eq_adjoint (A : matrix m n 𝕜) :
   to_lin' A.conj_transpose =
   @linear_map.adjoint 𝕜 (euclidean_space 𝕜 n) (euclidean_space 𝕜 m) _ _ _ _ _ _ _ (to_lin' A) :=
 begin
   rw @linear_map.eq_adjoint_iff _ (euclidean_space 𝕜 m) (euclidean_space 𝕜 n),
   intros x y,
   convert dot_product_assoc (conj ∘ (id x : m → 𝕜)) y A using 1,
   simp [dot_product, mul_vec, ring_hom.map_sum,  ← star_ring_end_apply, mul_comm],
 end
end matrix
-------------------------------

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n]

open_locale matrix

lemma matrix.pos_semidef.star_mul_self {n : Type*} [fintype n] (x : matrix n n 𝕜) :
  (xᴴ ⬝ x).pos_semidef :=
begin
  simp_rw [matrix.pos_semidef],
  split,
  { exact matrix.is_hermitian_transpose_mul_self _, },
  { intros y,
    have : is_R_or_C.re ((star y) ⬝ᵥ ((xᴴ ⬝ x).mul_vec y))
      = is_R_or_C.re ((star (x.mul_vec y)) ⬝ᵥ (x.mul_vec y)),
    { simp only [matrix.star_mul_vec, matrix.dot_product_mul_vec, matrix.vec_mul_vec_mul], },
    rw [this],
    clear this,
    simp_rw [matrix.dot_product, map_sum],
    apply finset.sum_nonneg',
    intros i,
    simp_rw [pi.star_apply, is_R_or_C.star_def, ← is_R_or_C.inner_apply],
    exact inner_self_nonneg, },
end

lemma matrix.pos_semidef.mul_star_self (x : matrix n n 𝕜) :
  (x ⬝ xᴴ).pos_semidef :=
begin
  simp_rw [matrix.pos_semidef],
  split,
  { exact matrix.is_hermitian_mul_conj_transpose_self _, },
  { intros y,
    have : is_R_or_C.re ((star y) ⬝ᵥ ((x ⬝ xᴴ).mul_vec y))
      = is_R_or_C.re ((star ((xᴴ).mul_vec y)) ⬝ᵥ ((xᴴ).mul_vec y)),
    { simp_rw [matrix.star_mul_vec, matrix.dot_product_mul_vec,
        matrix.conj_transpose_conj_transpose, matrix.vec_mul_vec_mul], },
    rw [this],
    clear this,
    simp_rw [matrix.dot_product, map_sum],
    apply finset.sum_nonneg',
    intros i,
    simp_rw [pi.star_apply, is_R_or_C.star_def, ← is_R_or_C.inner_apply],
    exact inner_self_nonneg, },
end

lemma matrix.to_euclidean_lin_eq_pi_Lp_linear_equiv [decidable_eq n] (x : matrix n n 𝕜) :
  x.to_euclidean_lin = ((pi_Lp.linear_equiv 2 𝕜 (λ _ : n, 𝕜)).symm.conj
    x.to_lin' : module.End 𝕜 (pi_Lp 2 _)) :=
rfl

lemma matrix.pos_semidef_eq_linear_map_positive [decidable_eq n] (x : matrix n n 𝕜) :
  (x.pos_semidef) ↔  x.to_euclidean_lin.is_positive :=
begin
  simp_rw [linear_map.is_positive, ← matrix.is_hermitian_iff_is_symmetric, matrix.pos_semidef, matrix.to_euclidean_lin_eq_pi_Lp_linear_equiv,
    pi_Lp.inner_apply, is_R_or_C.inner_apply, map_sum, linear_equiv.conj_apply,
    linear_map.comp_apply, linear_equiv.coe_coe, pi_Lp.linear_equiv_symm_apply,
    linear_equiv.symm_symm, pi_Lp.linear_equiv_apply, matrix.to_lin'_apply,
    pi_Lp.equiv_symm_apply, ← is_R_or_C.star_def, matrix.mul_vec, matrix.dot_product,
    pi_Lp.equiv_apply, ← pi.mul_apply (x _) _, ← matrix.dot_product, map_sum,
    pi.star_apply, matrix.mul_vec, matrix.dot_product, pi.mul_apply],
  exact ⟨λ h, h, λ h, h⟩,
end

lemma matrix.pos_semidef_iff [decidable_eq n] (x : matrix n n 𝕜) :
  x.pos_semidef ↔ ∃ y : matrix n n 𝕜, x = yᴴ ⬝ y :=
begin
  have : finite_dimensional.finrank 𝕜 (pi_Lp 2 (λ (_x : n), 𝕜)) = fintype.card n,
  { simp_rw [finrank_euclidean_space], },
  simp_rw [matrix.pos_semidef_eq_linear_map_positive,
    linear_map.is_positive_iff_exists_adjoint_mul_self _ this,
    matrix.to_euclidean_lin_eq_pi_Lp_linear_equiv,
    linear_equiv.conj_apply, linear_map.ext_iff, linear_map.comp_apply,
    linear_equiv.coe_coe, pi_Lp.linear_equiv_symm_apply, linear_equiv.symm_symm,
    pi_Lp.linear_equiv_apply, matrix.to_lin'_apply, function.funext_iff,
    pi_Lp.equiv_symm_apply, matrix.mul_vec, matrix.dot_product, pi_Lp.equiv_apply,
    matrix.ext_iff, matrix.mul_vec_eq, ← matrix.to_lin'_apply, matrix.to_lin'_mul,
    matrix.conj_transpose_eq_adjoint, matrix.to_lin'_apply, function.funext_iff,
    matrix.mul_vec, matrix.dot_product, linear_map.mul_eq_comp, linear_map.comp_apply],
  split,
  { rintros ⟨S, hS⟩,
    use S.to_matrix',
    intros c a,
    simp_rw [matrix.to_lin'_to_matrix', hS], },
  { rintros ⟨y, hy⟩,
    use y.to_lin',
    intros c a,
    exact hy c a, },
end

local notation `⟪` x `,` y `⟫_𝕜` := @inner 𝕜 _ _ x y

open_locale big_operators
lemma matrix.dot_product_eq_inner {n : Type*} [fintype n] (x y : n → 𝕜) :
  matrix.dot_product (star x) y = ∑ i : n, ⟪x i, y i⟫_𝕜 :=
rfl

lemma matrix.pos_semidef.invertible_iff_pos_def {n : Type*} [fintype n] [decidable_eq n]
  {x : matrix n n 𝕜} (hx : x.pos_semidef) :
  function.bijective x.to_lin' ↔ x.pos_def :=
begin
  simp_rw [matrix.pos_def, hx.1, true_and],
  cases (matrix.pos_semidef_iff x).mp hx with y hy,
  split,
  { intros h v hv,
    rw hy,
    have : is_R_or_C.re ((star v) ⬝ᵥ ((yᴴ ⬝ y).mul_vec v))
      = is_R_or_C.re ((star (y.mul_vec v)) ⬝ᵥ (y.mul_vec v)),
    { simp_rw [matrix.star_mul_vec, matrix.dot_product_mul_vec,
        matrix.vec_mul_vec_mul], },
    simp_rw [this, matrix.dot_product, map_sum, pi.star_apply, is_R_or_C.star_def,
      ← is_R_or_C.inner_apply, inner_self_eq_norm_sq_to_K],
    clear this,
    apply finset.sum_pos',
    { simp_rw [finset.mem_univ, forall_true_left],
      intros i,
      norm_cast,
      exact pow_two_nonneg _, },
    { simp_rw [finset.mem_univ, exists_true_left],
      suffices : y.mul_vec v ≠ 0,
      { simp_rw [ne.def, function.funext_iff, pi.zero_apply] at this,
        push_neg at this,
        cases this with j hj,
        rw ← norm_ne_zero_iff at hj,
        use j,
        norm_cast,
        exact (sq_pos_iff _).mpr hj, },
      by_contra',
      apply hv,
      apply_fun x.to_lin',
      { simp_rw [map_zero],
        rw matrix.mul_vec_eq at hy,
        specialize hy v,
        simp_rw [← matrix.mul_vec_mul_vec, this, matrix.mul_vec_zero] at hy,
        rw matrix.to_lin'_apply,
        exact hy, },
      { exact h.1, }, }, },
  { intros h,
    by_contra',
    rw [function.bijective, ← linear_map.injective_iff_surjective, and_self,
        injective_iff_map_eq_zero] at this,
    push_neg at this,
    cases this with a ha,
    specialize h a ha.2,
    rw [← matrix.to_lin'_apply, ha.1, matrix.dot_product_zero, is_R_or_C.zero_re', lt_self_iff_false] at h,
    exact h, },
end

lemma matrix.is_hermitian_self_mul_conj_transpose (A : matrix n n 𝕜) :
  (A.conj_transpose.mul A).is_hermitian :=
by rw [matrix.is_hermitian, matrix.conj_transpose_mul, matrix.conj_transpose_conj_transpose]

lemma matrix.trace_star {A : matrix n n 𝕜} :
  star A.trace = Aᴴ.trace :=
begin
  simp_rw [matrix.trace, matrix.diag, star_sum, matrix.conj_transpose_apply],
end

lemma matrix.nonneg_eigenvalues_of_pos_semidef
  [decidable_eq n] {μ : ℝ} {A : matrix n n 𝕜}
  (hμ : module.End.has_eigenvalue A.to_euclidean_lin ↑μ)
  (H : A.pos_semidef) : 0 ≤ μ :=
begin
  apply eigenvalue_nonneg_of_nonneg hμ,
  simp_rw [matrix.to_euclidean_lin_eq_to_lin, matrix.to_lin_apply,
           inner_sum, inner_smul_right, pi_Lp.basis_fun_apply,
           pi_Lp.equiv_symm_single, euclidean_space.inner_single_right, one_mul],
  intros x,
  have : ∑ (x_1 : n), A.mul_vec (((pi_Lp.basis_fun 2 𝕜 n).repr) x) x_1 * (star_ring_end ((λ (i : n), 𝕜) x_1)) (x x_1) = matrix.dot_product (star x) (A.mul_vec x),
  { simp_rw [mul_comm, matrix.dot_product],
    congr, },
  rw this,
  exact H.2 _,
end

lemma matrix.is_hermitian.nonneg_eigenvalues_of_pos_semidef [decidable_eq n]
  [decidable_eq 𝕜] {A : matrix n n 𝕜} (hA : A.pos_semidef) (i : n) :
  0 ≤ hA.1.eigenvalues i :=
matrix.nonneg_eigenvalues_of_pos_semidef (hA.1.eigenvalues_has_eigenvalue _) hA

@[instance] noncomputable def matrix.pos_def.invertible [decidable_eq n] {Q : matrix n n 𝕜}
  (hQ : Q.pos_def) : invertible Q :=
begin
  suffices : function.bijective Q.to_lin',
  { have h : invertible Q.to_lin',
    { refine is_unit.invertible _,
      rw linear_map.is_unit_iff_ker_eq_bot,
      exact linear_map.ker_eq_bot_of_injective this.1, },
    refine is_unit.invertible _,
    rw matrix.is_unit_iff_is_unit_det,
    rw ← linear_map.det_to_lin',
    apply linear_map.is_unit_det,
    rw ← nonempty_invertible_iff_is_unit,
    exact nonempty.intro h, },
  rw [matrix.pos_semidef.invertible_iff_pos_def hQ.pos_semidef],
  exact hQ,
end

lemma matrix.mul_vec_sum {n : Type*} [fintype n] (x : matrix n n 𝕜) (y : n → (n → 𝕜)):
  x.mul_vec (∑ i : n, y i) = ∑ i : n, x.mul_vec (y i) :=
begin
  ext1,
  simp only [finset.sum_apply, matrix.mul_vec, matrix.dot_product, finset.mul_sum],
  rw finset.sum_comm,
end

open matrix
open_locale matrix

variables {E : Type*} [normed_add_comm_group E]

lemma matrix.to_lin_pi_Lp_eq_to_lin' {n : Type*} [fintype n] [decidable_eq n] :
  to_lin (pi_Lp.basis_fun 2 𝕜 n) (pi_Lp.basis_fun 2 𝕜 n) = to_lin' :=
rfl

lemma matrix.pos_semidef_iff_eq_rank_one {n : ℕ} [decidable_eq 𝕜] {x : matrix (fin n) (fin n) 𝕜} :
  x.pos_semidef ↔ ∃ (m : ℕ) (v : fin m → euclidean_space 𝕜 (fin n)),
    x = ∑ i : fin m, (((rank_one (v i) (v i)
      : euclidean_space 𝕜 (fin n) →L[𝕜] euclidean_space 𝕜 (fin n))
      : euclidean_space 𝕜 (fin n) →ₗ[𝕜] euclidean_space 𝕜 (fin n))).to_matrix' :=
begin
  have : finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 (fin n)) = n :=
  finrank_euclidean_space_fin,
  simp_rw [pos_semidef_eq_linear_map_positive, linear_map.is_positive_iff_eq_sum_rank_one this,
    to_euclidean_lin_eq_to_lin, matrix.to_lin_pi_Lp_eq_to_lin', ← map_sum],
  split; rintros ⟨m, y, hy⟩; refine ⟨m, y, _⟩,
  { simp_rw [← hy, linear_map.to_matrix'_to_lin'], },
  { rw [hy, to_lin'_to_matrix'], },
end

/-- a matrix $x$ is positive semi-definite if and only if there exists vectors $(v_i)$ such that
  $\sum_i v_iv_i^*=x$  -/
lemma matrix.pos_semidef_iff_col_mul_conj_transpose_col [decidable_eq n] [decidable_eq 𝕜]
  (x : matrix n n 𝕜) :
  x.pos_semidef ↔ ∃ (v : n → (n → 𝕜)),
    ∑ (i : n), col (v i) ⬝ (col (v i))ᴴ = x :=
begin
  simp_rw [conj_transpose_col],
  split,
  { intros hx,
    simp_rw [mul_vec_eq],
    let a : matrix n n 𝕜 :=
    λ i j, (real.sqrt (hx.1.eigenvalues i)) • (hx.1.eigenvector_basis i) j,
    use a,
    intros u,
    ext1 j,
    nth_rewrite_rhs 0 ← continuous_linear_map.one_apply u,
    rw ← euclidean_space.rank_one_of_orthonormal_basis_eq_one hx.1.eigenvector_basis,
    simp_rw [continuous_linear_map.sum_apply, rank_one_apply, mul_vec_sum, mul_vec_smul,
      hx.1.apply_eigenvector_basis],
    simp only [mul_vec, dot_product, finset.sum_apply, finset.sum_mul, finset.sum_smul,
      finset.sum_apply, pi.smul_apply, mul_apply, col_apply, row_apply, smul_eq_mul,
      mul_smul_comm, euclidean_space.inner_eq],
    rw finset.sum_comm,
    apply finset.sum_congr rfl, intros,
    apply finset.sum_congr rfl, intros,
    simp only [fintype.univ_punit, finset.sum_const, finset.card_singleton, nsmul_eq_mul,
        algebra_map.coe_one, one_mul],
    simp_rw [pi.star_apply, a, is_R_or_C.real_smul_eq_coe_mul, star_mul',
      is_R_or_C.star_def, is_R_or_C.conj_of_real, mul_mul_mul_comm, ← is_R_or_C.of_real_mul,
      ← real.sqrt_mul (nonneg_eigenvalues_of_pos_semidef (hx.1.eigenvalues_has_eigenvalue _) hx),
      ← pow_two, real.sqrt_sq (nonneg_eigenvalues_of_pos_semidef
        (hx.1.eigenvalues_has_eigenvalue _) hx)],
    ring_nf, },
  { rintros ⟨v, hv⟩,
    rw [pos_semidef],
    have : x.is_hermitian,
    { simp_rw [is_hermitian, ← hv, conj_transpose_sum, conj_transpose_mul, conj_transpose_row,
      conj_transpose_col, star_star], },
    { refine ⟨this, _⟩,
      intros y,
      have : ∀ x, v x ⬝ᵥ star y = star (y ⬝ᵥ star (v x)),
      { intros, simp_rw [← star_dot_product_star, star_star], },
      simp_rw [← trace_col_mul_row, row_mul_vec, transpose_mul, transpose_col, ← matrix.mul_assoc,
        ← hv, transpose_sum, matrix.mul_sum, transpose_mul, transpose_col, transpose_row,
        trace_sum, map_sum, ← matrix.mul_assoc, trace_mul_comm _ (row (v _)), ← matrix.mul_assoc,
        matrix.trace, diag, matrix.mul_assoc _ (row y),
        @mul_apply _ _ _ _ _ _ _ ((row (v _)) ⬝ (col (star y))) _, row_mul_col_apply,
        this],
      simp only [fintype.univ_punit, finset.sum_const, finset.card_singleton, nsmul_eq_mul,
        algebra_map.coe_one, one_mul, is_R_or_C.star_def, is_R_or_C.conj_mul],
      apply finset.sum_nonneg,
      intros,
      norm_cast,
      exact is_R_or_C.norm_sq_nonneg _, }, },
end

lemma vec_mul_vec.pos_semidef [decidable_eq n] [decidable_eq 𝕜] (x : n → 𝕜) :
  (vec_mul_vec x (star x)).pos_semidef :=
begin
  rw matrix.pos_semidef_iff_col_mul_conj_transpose_col,
  by_cases nonempty n,
  { let i : n := nonempty.some h,
    let v : n → n → 𝕜 := λ j k, ite (i = j) (x k) 0,
    use v,
    simp_rw [v, ← matrix.ext_iff, matrix.sum_apply, mul_apply, col_apply,
      conj_transpose_apply, col_apply, star_ite, star_zero, ite_mul, zero_mul,
      mul_ite, mul_zero, finset.sum_ite_irrel, finset.sum_const_zero,
      finset.sum_ite_eq, finset.mem_univ, if_true, eq_self_iff_true,
      if_true, finset.sum_const],
    intros,
    simp only [fintype.univ_punit, finset.card_singleton, is_R_or_C.star_def,
      nsmul_eq_mul, algebra_map.coe_one, one_mul],
    simp_rw [vec_mul_vec_apply, pi.star_apply, is_R_or_C.star_def], },
  { rw not_nonempty_iff at h,
    haveI : is_empty n := h,
    simp only [eq_iff_true_of_subsingleton, exists_const], },
end

variables {M₁ M₂ : Type*} [normed_add_comm_group M₁] [normed_add_comm_group M₂]
  [inner_product_space ℂ M₁] [inner_product_space ℂ M₂]

/-- we say a linear map $T \colon L(M_1) \to L(M_2)$ is a positive map
  if for all positive $x \in L(M_1)$, we also get $T(x)$ is positive  -/
def linear_map.positive_map (T : (M₁ →ₗ[ℂ] M₁) →ₗ[ℂ] (M₂ →ₗ[ℂ] M₂)) :
  Prop :=
∀ x : M₁ →ₗ[ℂ] M₁, x.is_positive → (T x).is_positive

/-- a $^*$-homomorphism from $L(M_1)$ to $L(M_2)$ is a positive map -/
lemma linear_map.positive_map.star_hom {n₁ : ℕ}
  [finite_dimensional ℂ M₁] [finite_dimensional ℂ M₂]
  (hn₁ : finite_dimensional.finrank ℂ M₁ = n₁)
  (φ : star_alg_hom ℂ (M₁ →ₗ[ℂ] M₁) (M₂ →ₗ[ℂ] M₂)) :
  φ.to_alg_hom.to_linear_map.positive_map :=
begin
  intros x hx,
  rcases (linear_map.is_positive_iff_exists_adjoint_mul_self x hn₁).mp hx with ⟨w, rfl⟩,
  have : ∀ h, φ.to_alg_hom.to_linear_map h = φ h := λ h, rfl,
  simp_rw [linear_map.is_positive, linear_map.is_symmetric, this, _root_.map_mul,
    ← linear_map.star_eq_adjoint, map_star, linear_map.mul_apply, linear_map.star_eq_adjoint,
    linear_map.adjoint_inner_left, linear_map.adjoint_inner_right, eq_self_iff_true,
    forall_2_true_iff, true_and, inner_self_nonneg, forall_const],
end

/-- the identity is a positive definite matrix -/
lemma matrix.pos_def_one [decidable_eq n] :
  (1 : matrix n n 𝕜).pos_def :=
begin
  simp_rw [matrix.pos_def, matrix.is_hermitian, matrix.conj_transpose_one,
           eq_self_iff_true, true_and, matrix.one_mul_vec,
           matrix.dot_product_eq_inner, ← matrix.vec_ne_zero, map_sum],
  intros x h,
  apply finset.sum_pos',
  simp only [finset.mem_univ, forall_true_left],
  intros i,
  exact inner_self_nonneg,
  cases h with i hi,
  use i,
  simp_rw [finset.mem_univ, true_and],
  simp_rw [ne.def] at hi,
  contrapose! hi,
  rw inner_self_nonpos at hi,
  exact hi,
end

/-- each eigenvalue of a positive definite matrix is positive -/
lemma matrix.pos_def.pos_eigenvalues [decidable_eq 𝕜] [decidable_eq n]
  {A : matrix n n 𝕜} (hA : A.pos_def) (i : n) :
  0 < hA.is_hermitian.eigenvalues i :=
begin
  letI := hA,
  have := matrix.nonneg_eigenvalues_of_pos_semidef
    (matrix.is_hermitian.eigenvalues_has_eigenvalue hA.1 i)
    (matrix.pos_def.pos_semidef hA),
  suffices t1 : 0 ≠ hA.is_hermitian.eigenvalues i,
  { contrapose t1,
    push_neg,
    exact eq_iff_le_not_lt.mpr (and.intro this t1), },
  have : function.injective A.to_lin' :=
  ((matrix.pos_semidef.invertible_iff_pos_def hA.pos_semidef).mpr hA).1,
  have : function.injective A.to_euclidean_lin,
  { rw matrix.to_euclidean_lin_eq_pi_Lp_linear_equiv,
    exact this, },
  cases module.End.has_eigenvector_iff_has_eigenvalue.mpr
    (matrix.is_hermitian.eigenvalues_has_eigenvalue hA.1 i) with v hv,
  intros h,
  simp_rw [← h, is_R_or_C.of_real_zero, zero_smul] at hv,
  exact ((map_ne_zero_iff _ this).mpr hv.2) hv.1,
end

lemma matrix.pos_def.pos_trace [decidable_eq n] [decidable_eq 𝕜]
  [nonempty n] {x : matrix n n 𝕜} (hx : x.pos_def) :
  0 < is_R_or_C.re x.trace :=
begin
  simp_rw [is_hermitian.trace_eq hx.1, map_sum, is_R_or_C.of_real_re],
  apply finset.sum_pos,
  { exact λ _ _, hx.pos_eigenvalues _, },
  { exact finset.univ_nonempty, },
end

/-- the trace of a positive definite matrix is non-zero -/
lemma matrix.pos_def.trace_ne_zero [decidable_eq n] [nonempty n]
  [decidable_eq 𝕜] {x : matrix n n 𝕜} (hx : x.pos_def) :
  x.trace ≠ 0 :=
begin
  rw matrix.is_hermitian.trace_eq hx.is_hermitian,
  norm_num,
  rw [← is_R_or_C.of_real_sum, is_R_or_C.of_real_eq_zero,
    finset.sum_eq_zero_iff_of_nonneg _],
  { simp_rw [finset.mem_univ, true_implies_iff],
    simp only [not_forall],
    use _inst_9.some,
    exact norm_num.ne_zero_of_pos _
      (matrix.pos_def.pos_eigenvalues hx _), },
  { intros,
    exact le_of_lt (matrix.pos_def.pos_eigenvalues hx _), },
end

open_locale complex_order
lemma pos_semidef.complex [decidable_eq n] (x : matrix n n ℂ) :
  x.pos_semidef ↔ ∀ y : n → ℂ,
    0 ≤ (star y ⬝ᵥ x.mul_vec y) :=
    -- ((star y ⬝ᵥ x.mul_vec y).re : ℂ) = star y ⬝ᵥ x.mul_vec y ∧ 0 ≤ (star y ⬝ᵥ x.mul_vec y).re :=
begin
  simp_rw [pos_semidef_eq_linear_map_positive x, linear_map.complex_is_positive,
    is_R_or_C.nonneg_def'],
  refl,
end

lemma std_basis_matrix.sum_eq_one [decidable_eq n] (a : 𝕜) :
  ∑ k : n, std_basis_matrix k k a = a • 1 :=
by simp_rw [← matrix.ext_iff, matrix.sum_apply, pi.smul_apply,
  std_basis_matrix, one_apply, smul_ite, ite_and, finset.sum_ite_eq',
  finset.mem_univ, if_true, smul_eq_mul, mul_zero, mul_one, eq_self_iff_true,
  forall_2_true_iff]

lemma std_basis_matrix_mul [decidable_eq n] (i j k l : n) (a b : 𝕜) :
  std_basis_matrix i j a ⬝ std_basis_matrix k l b
    = ite (j = k) (1 : 𝕜) (0 : 𝕜) • std_basis_matrix i l (a * b) :=
begin
  ext1,
  simp_rw [mul_apply, std_basis_matrix, ite_mul, zero_mul, mul_ite, mul_zero, pi.smul_apply,
    ite_and, finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ,
    if_true, ← ite_and, ← and_assoc, ite_smul, zero_smul, one_smul, ← ite_and, ← and_assoc,
    and_comm (j = k), eq_comm],
end

lemma matrix.smul_std_basis_matrix' {n R : Type*} [comm_semiring R] [decidable_eq n] (i j : n) (c : R) :
  std_basis_matrix i j c = c • std_basis_matrix i j 1 :=
begin
  rw [smul_std_basis_matrix, smul_eq_mul, mul_one],
end

lemma matrix.trace_iff' (x : matrix n n 𝕜) :
  x.trace = ∑ i : n, x i i :=
rfl

lemma exists_unique_trace [decidable_eq n] [nontrivial n] :
  ∃! φ : matrix n n 𝕜 →ₗ[𝕜] 𝕜, (∀ a b : matrix n n 𝕜, φ (a ⬝ b) = φ (b ⬝ a)) ∧ φ 1 = 1 :=
begin
  use (1 / fintype.card n : 𝕜) • trace_linear_map n 𝕜 𝕜,
  have trace_functional_iff : ∀ (φ : matrix n n 𝕜 →ₗ[𝕜] 𝕜),
    ((∀ a b : matrix n n 𝕜, φ (a ⬝ b) = φ (b ⬝ a)) ∧ (φ (1) = 1))
    ↔ φ = (1 / fintype.card n : 𝕜) • trace_linear_map n 𝕜 𝕜 :=
  begin
    intros,
    have : (↑(fintype.card n) : 𝕜)⁻¹ * ↑(finset.univ.card) = 1,
    { rw inv_mul_eq_one₀,
      { refl, },
      { simp only [ne.def, nat.cast_eq_zero, fintype.card_ne_zero],
        exact not_false, }, },
    split,
    { intros h,
      rw linear_map.ext_iff,
      intros x,
      have : ∀ i j : n, φ (std_basis_matrix i j (1 : 𝕜))
        = (1 / (fintype.card n : 𝕜)) • ite (j = i) (1 : 𝕜) (0 : 𝕜),
      { intros i j,
        calc φ (std_basis_matrix i j (1 : 𝕜))
          = (1 / (fintype.card n : 𝕜))
            • ∑ k, φ (std_basis_matrix i k 1 ⬝ (std_basis_matrix k j 1 : matrix n n 𝕜)) : _
          ... = (1 / (fintype.card n : 𝕜))
            • ∑ k, φ (std_basis_matrix k j 1 ⬝ std_basis_matrix i k 1) : _
          ... = (1 / (fintype.card n : 𝕜)) • ite (j = i) (φ (∑ k, std_basis_matrix k k 1)) 0 : _
          ... = (1 / (fintype.card n : 𝕜)) • ite (j = i) (φ 1) 0 : _
          ... = (1 / (fintype.card n : 𝕜)) • ite (j = i) 1 0 : _,
        { simp_rw [std_basis_matrix.mul_same, one_mul],
          simp only [one_div, finset.sum_const, nsmul_eq_mul, algebra.id.smul_eq_mul],
          rw [← mul_assoc],
          simp_rw [this, one_mul], },
        { simp_rw h.1, },
        { simp_rw [std_basis_matrix_mul, one_mul, smul_hom_class.map_smul,
            smul_eq_mul, boole_mul, finset.sum_ite_irrel, finset.sum_const_zero,
            map_sum], },
        { simp_rw [std_basis_matrix.sum_eq_one, one_smul], },
        { simp_rw h.2, }, },
      rw [linear_map.smul_apply, trace_linear_map_apply],
      nth_rewrite_lhs 0 matrix_eq_sum_std_basis x,
      simp_rw [matrix.smul_std_basis_matrix' _ _ (x _ _), map_sum, smul_hom_class.map_smul],
      calc ∑ x_1 x_2, x x_1 x_2 • φ (std_basis_matrix x_1 x_2 1)
        = ∑ x_1 x_2, x x_1 x_2 • (1 / (fintype.card n : 𝕜)) • ite (x_2 = x_1) (1 : 𝕜) 0 : _
        ... = ∑ x_1, x x_1 x_1 • (1 / fintype.card n : 𝕜) : _
        ... = (1 / fintype.card n : 𝕜) • x.trace : _,
      { simp_rw ← this, },
      { simp_rw [smul_ite, smul_zero, finset.sum_ite_eq', finset.mem_univ, if_true,
          smul_eq_mul, mul_one], },
      { simp_rw [← finset.sum_smul, matrix.trace_iff' x, smul_eq_mul, mul_comm], }, },
    { rintros rfl,
      simp_rw [linear_map.smul_apply, trace_linear_map_apply, matrix.trace_iff' 1, one_apply_eq,
        finset.sum_const, one_div, nsmul_eq_mul, mul_one],
      refine ⟨λ x y, _, this⟩,
      rw trace_mul_comm, },
  end,
  simp only [trace_functional_iff, imp_self, forall_true_iff, and_true],
end

lemma matrix.std_basis_matrix.trace [decidable_eq n] (i j : n) (a : 𝕜) :
  (std_basis_matrix i j a).trace = ite (i = j) a 0 :=
by simp_rw [matrix.trace_iff', std_basis_matrix, ite_and, finset.sum_ite_eq, finset.mem_univ,
  if_true, eq_comm]

lemma matrix.std_basis_matrix_eq {n : Type*} [decidable_eq n] (i j : n) (a : 𝕜) :
  std_basis_matrix i j a = λ (i' j' : n), ite (i = i' ∧ j = j') a 0 :=
rfl

lemma vec_mul_vec_eq_zero_iff (x : n → 𝕜) :
  vec_mul_vec x (star x) = 0 ↔ x = 0 :=
begin
  simp_rw [← matrix.ext_iff, vec_mul_vec_apply, dmatrix.zero_apply,
    pi.star_apply, mul_comm _ (star _), function.funext_iff, pi.zero_apply],
  split,
  { intros h i,
    specialize h i i,
    rw [is_R_or_C.star_def, is_R_or_C.conj_mul, is_R_or_C.of_real_eq_zero,
      is_R_or_C.norm_sq_eq_zero] at h,
    exact h, },
  { intros h i j,
    simp_rw [h, mul_zero], },
end

lemma matrix.pos_def.diagonal [decidable_eq n] (x : n → 𝕜) :
  (diagonal x).pos_def ↔ ∀ i, 0 < is_R_or_C.re (x i) ∧ (is_R_or_C.re (x i) : 𝕜) = x i :=
begin
  split,
  { intros h i,
    have h' := h.2,
    simp only [dot_product, mul_vec, diagonal, ite_mul, of_apply, zero_mul, finset.sum_ite_eq,
      finset.mem_univ, if_true] at h',
    let g : n → 𝕜 := λ p, ite (i = p) 1 0,
    have : g ≠ 0,
    { rw [ne.def, function.funext_iff, not_forall],
      simp_rw [pi.zero_apply],
      use i,
      simp_rw [g, eq_self_iff_true, if_true],
      exact one_ne_zero, },
    specialize h' g this,
    simp_rw [mul_rotate', pi.star_apply, g, star_ite, star_zero, star_one, boole_mul, ← ite_and,
      and_self, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at h',
    split,
    { exact h', },
    { have := h.1,
      simp_rw [is_hermitian, diagonal_conj_transpose, diagonal_eq_diagonal_iff,
        pi.star_apply, is_R_or_C.star_def, is_R_or_C.conj_eq_iff_re] at this,
      exact this i, }, },
  { intros h,
    split,
    { simp_rw [is_hermitian, diagonal_conj_transpose, diagonal_eq_diagonal_iff, pi.star_apply,
        is_R_or_C.star_def, is_R_or_C.conj_eq_iff_re],
      intros,
      exact (h _).2, },
    { intros y hy,
      simp only [mul_vec, dot_product_diagonal, dot_product, diagonal, ite_mul, zero_mul, mul_ite,
        mul_zero, of_apply, finset.sum_ite_eq, finset.mem_univ, if_true],
      simp_rw [pi.star_apply, mul_rotate' (star (y _)), mul_comm (y _),
        is_R_or_C.star_def, is_R_or_C.conj_mul, map_sum, mul_comm (x _),
        is_R_or_C.of_real_mul_re],
      apply finset.sum_pos',
      intros,
      exact mul_nonneg (is_R_or_C.norm_sq_nonneg _) (le_of_lt (h _).1),
      { simp_rw [ne.def, function.funext_iff, pi.zero_apply, not_forall] at hy,
        obtain ⟨i,hi⟩ := hy,
        exact ⟨i, finset.mem_univ _, mul_pos (is_R_or_C.norm_sq_pos.mpr hi) (h _).1⟩, }, }, },
end

lemma matrix.pos_semidef.diagonal [decidable_eq n] (x : n → 𝕜) :
  (diagonal x).pos_semidef ↔ ∀ i, 0 ≤ is_R_or_C.re (x i) ∧ (is_R_or_C.re (x i) : 𝕜) = x i :=
begin
  split,
  { intros h i,
    have h' := h.2,
    simp only [dot_product, mul_vec, diagonal, ite_mul, of_apply, zero_mul, finset.sum_ite_eq,
      finset.mem_univ, if_true] at h',
    let g : n → 𝕜 := λ p, ite (i = p) 1 0,
    specialize h' g,
    simp_rw [mul_rotate', pi.star_apply, g, star_ite, star_zero, star_one, boole_mul, ← ite_and,
      and_self, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at h',
    split,
    { exact h', },
    { have := h.1,
      simp_rw [is_hermitian, diagonal_conj_transpose, diagonal_eq_diagonal_iff,
        pi.star_apply, is_R_or_C.star_def, is_R_or_C.conj_eq_iff_re] at this,
      exact this i, }, },
  { intros h,
    split,
    { simp_rw [is_hermitian, diagonal_conj_transpose, diagonal_eq_diagonal_iff, pi.star_apply,
        is_R_or_C.star_def, is_R_or_C.conj_eq_iff_re],
      intros,
      exact (h _).2, },
    { intros y,
      simp only [mul_vec, dot_product_diagonal, dot_product, diagonal, ite_mul, zero_mul, mul_ite,
        mul_zero, of_apply, finset.sum_ite_eq, finset.mem_univ, if_true],
      simp_rw [pi.star_apply, mul_rotate' (star (y _)), mul_comm (y _),
        is_R_or_C.star_def, is_R_or_C.conj_mul, map_sum, mul_comm (x _),
        is_R_or_C.of_real_mul_re],
      apply finset.sum_nonneg',
      intros,
      exact mul_nonneg (is_R_or_C.norm_sq_nonneg _) (h _).1, }, },
end

namespace matrix

lemma trace_conj_transpose_mul_self_re_nonneg (x : matrix n n 𝕜) :
  0 ≤ is_R_or_C.re (xᴴ ⬝ x).trace :=
begin
  simp_rw [matrix.trace, matrix.diag, map_sum, matrix.mul_apply, matrix.conj_transpose_apply,
    map_sum],
  apply finset.sum_nonneg',
  intros i,
  apply finset.sum_nonneg',
  intros j,
  simp_rw [is_R_or_C.star_def, ← is_R_or_C.inner_apply],
  exact inner_self_nonneg,
end

lemma pos_semidef.trace_conj_transpose_mul_self_nonneg [decidable_eq n]
  {Q : matrix n n 𝕜} (x : matrix n n 𝕜) (hQ : Q.pos_semidef) :
  (is_R_or_C.re (Q ⬝ xᴴ ⬝ x).trace : 𝕜) = (Q ⬝ xᴴ ⬝ x).trace
    ∧ 0 ≤ is_R_or_C.re (Q ⬝ xᴴ ⬝ x).trace :=
begin
  rcases (matrix.pos_semidef_iff Q).mp hQ with ⟨y, rfl⟩,
  rw [matrix.trace_mul_cycle, ← matrix.mul_assoc],
  nth_rewrite 0 ← conj_transpose_conj_transpose x,
  nth_rewrite 2 ← conj_transpose_conj_transpose x,
  nth_rewrite 4 ← conj_transpose_conj_transpose x,
  rw [← matrix.conj_transpose_mul],
  simp_rw [matrix.mul_assoc, ← is_R_or_C.conj_eq_iff_re,
    star_ring_end_apply, trace_star],
  rw [conj_transpose_mul, conj_transpose_conj_transpose],
  refine ⟨rfl, trace_conj_transpose_mul_self_re_nonneg _⟩,
end

/-- given a positive definite matrix $Q$, we have
  $0\leq\Re(\textnormal{Tr}(Qx^*x))$ for any matrix $x$ -/
lemma nontracial.trace_conj_transpose_mul_self_re_nonneg [decidable_eq n]
  {Q : matrix n n 𝕜} (x : matrix n n 𝕜) (hQ : Q.pos_def) :
  0 ≤ is_R_or_C.re (Q ⬝ xᴴ ⬝ x).trace :=
(hQ.pos_semidef.trace_conj_transpose_mul_self_nonneg _).2

open_locale big_operators

@[simp] lemma finset.sum_abs_eq_zero_iff' {s : Type*} [fintype s] {x : s → 𝕜} :
  ∑ (i : s) in finset.univ, ‖x i‖ ^ 2 = 0
    ↔ ∀ (i : s), ‖x i‖ ^ 2 = 0 :=
begin
  have : ∀ i : s, 0 ≤ ‖x i‖ ^ 2 := λ i, sq_nonneg _,
  split,
  { intros h i,
    have h' : ∀ (i : s), i ∈ _  → 0 ≤ ‖(x i)‖ ^ 2,
    { intros i hi, exact this _, },
    have h'' : ∑ (i : s) in _, ‖(x i: 𝕜)‖ ^ 2 = 0 := h,
    rw [finset.sum_eq_zero_iff_of_nonneg h'] at h'',
    simp only [finset.mem_univ, is_R_or_C.norm_sq_eq_zero, forall_true_left] at h'',
    exact h'' i, },
  { intros h,
    simp_rw [h, finset.sum_const_zero], },
end

lemma trace_conj_transpose_mul_self_eq_zero (x : matrix n n 𝕜) :
  (xᴴ ⬝ x).trace = 0 ↔ x = 0 :=
begin
  split,
  { simp_rw [← matrix.ext_iff, dmatrix.zero_apply, matrix.trace, matrix.diag,
      matrix.mul_apply, matrix.conj_transpose_apply, is_R_or_C.star_def,
      is_R_or_C.conj_mul, is_R_or_C.norm_sq_eq_def', is_R_or_C.of_real_pow],
    norm_cast,
    rw finset.sum_comm,
    simp_rw [← finset.sum_product', finset.univ_product_univ, finset.sum_abs_eq_zero_iff',
      pow_eq_zero_iff two_pos, norm_eq_zero],
    intros h i j,
    exact h (i,j), },
  { intros h,
    simp_rw [h, matrix.mul_zero, matrix.trace_zero], },
end

/-- given a positive definite matrix $Q$, we get
  $\textnormal{Tr}(Qx^*x)=0$ if and only if $x=0$ for any matrix $x$ -/
lemma nontracial.trace_conj_transpose_mul_self_eq_zero [decidable_eq n]
  {x Q : matrix n n 𝕜} (hQ : Q.pos_def) :
  (Q ⬝ xᴴ ⬝ x).trace = 0 ↔ x = 0 :=
begin
  rcases (pos_semidef_iff Q).mp hQ.pos_semidef with ⟨y, rfl⟩,
  rw [trace_mul_cycle, ← matrix.mul_assoc],
  nth_rewrite 0 ← conj_transpose_conj_transpose x,
  rw [← conj_transpose_mul],
  simp_rw [matrix.mul_assoc],
  rw trace_conj_transpose_mul_self_eq_zero _,
  refine ⟨λ h, _, λ h, by rw [h, conj_transpose_zero, matrix.mul_zero]⟩,
  rw [← star_eq_zero, mul_vec_eq],
  intros u,
  apply_fun (yᴴ ⬝ y).to_lin',
  simp_rw [← to_lin'_apply, ← linear_map.comp_apply, ← to_lin'_mul,
    ← mul_eq_mul, mul_assoc, mul_eq_mul, star_eq_conj_transpose],
  rw [h],
  simp_rw [matrix.mul_zero],
  refine function.bijective.injective _,
  rw [matrix.pos_semidef.invertible_iff_pos_def hQ.pos_semidef],
  exact hQ,
end

lemma is_hermitian.trace_conj_symm_star_mul {Q : matrix n n 𝕜} (hQ : Q.is_hermitian)
  (x y : matrix n n 𝕜) :
  (star_ring_end 𝕜) (Q ⬝ yᴴ ⬝ x).trace = (Q ⬝ xᴴ ⬝ y).trace :=
begin
  simp_rw [star_ring_end_apply, ← trace_conj_transpose, conj_transpose_mul,
    conj_transpose_conj_transpose, hQ.eq, matrix.mul_assoc],
  rw [trace_mul_cycle'],
end

lemma conj_transpose_mul_self_eq_zero (x : matrix n n 𝕜) :
  xᴴ ⬝ x = 0 ↔ x = 0 :=
begin
  refine ⟨_, λ h, by rw [h, matrix.mul_zero]⟩,
  simp_rw [← matrix.ext_iff, mul_apply, conj_transpose_apply, pi.zero_apply],
  intros h i j,
  specialize h j j,
  simp_rw [is_R_or_C.star_def, is_R_or_C.conj_mul, is_R_or_C.norm_sq_eq_def',
    ← is_R_or_C.of_real_sum, ← @is_R_or_C.of_real_zero 𝕜, is_R_or_C.of_real_inj,
      finset.sum_abs_eq_zero_iff', sq_eq_zero_iff, norm_eq_zero] at h,
  exact h i,
end

lemma pos_semidef_smul_iff {x : matrix n n 𝕜} (hx : x.pos_semidef) (α : nnreal) :
  (((α : ℝ) : 𝕜) • x).pos_semidef :=
begin
  split,
  { calc (((α : ℝ) : 𝕜) • x)ᴴ = star ((α : ℝ) : 𝕜) • xᴴ : by rw conj_transpose_smul
      ... = ((α : ℝ) : 𝕜) • x : by rw [is_R_or_C.star_def, is_R_or_C.conj_of_real, hx.1.eq], },
  intros x,
  simp_rw [smul_mul_vec_assoc, dot_product_smul, smul_eq_mul, is_R_or_C.of_real_mul_re,
    mul_nonneg (nnreal.coe_nonneg _) (hx.2 _)],
end

end matrix

open matrix
open_locale matrix
lemma rank_one.euclidean_space.to_matrix' {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*}
  [fintype n] [decidable_eq n] (x y : euclidean_space 𝕜 n) :
  ((@rank_one 𝕜 (euclidean_space 𝕜 n) _ _ _ x y)
    : euclidean_space 𝕜 n →ₗ[𝕜] euclidean_space 𝕜 n).to_matrix'
      = col (x : n → 𝕜) ⬝ (col (y : n → 𝕜))ᴴ :=
begin
  simp_rw [← matrix.ext_iff, linear_map.to_matrix'_apply, continuous_linear_map.coe_coe,
    rank_one_apply, pi.smul_apply, euclidean_space.inner_eq, dot_product, mul_boole,
    finset.sum_ite_eq', finset.mem_univ, if_true, mul_apply, conj_transpose_apply,
    col_apply, smul_eq_mul, fintype.univ_punit, finset.sum_const, finset.card_singleton,
    nsmul_eq_mul, algebra_map.coe_one, one_mul, mul_comm, pi.star_apply, eq_self_iff_true,
    forall_2_true_iff],
end

namespace matrix

lemma pos_semidef.col_mul_conj_transpose_col {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n]
  [decidable_eq n] [decidable_eq 𝕜] (x : n → 𝕜) :
  (col x ⬝ (col x)ᴴ : matrix n n 𝕜).pos_semidef :=
begin
  simp_rw [pos_semidef_iff_col_mul_conj_transpose_col, conj_transpose_col],
  by_cases nonempty n,
  { obtain i := h.some,
    let v : n → (n → 𝕜) := λ j, ite (j = i) x 0,
    use v,
    simp_rw [v, ← ext_iff, sum_apply, mul_apply, col_apply, row_apply,
      pi.star_apply, fintype.univ_punit, finset.sum_const, finset.card_singleton, one_smul,
      ite_apply, pi.zero_apply, star_ite, star_zero, mul_ite, mul_zero, ite_mul, zero_mul,
      finset.sum_ite_eq', finset.mem_univ, if_true, eq_self_iff_true, ite_eq_left_iff,
      not_true, false_implies_iff, forall_2_true_iff], },
  { simp_rw [not_nonempty_iff] at h,
    have : x = 0,
    { ext1 i,
      exfalso,
      exact (is_empty_iff.mp h) i, },
    use 0,
    simp only [this, ← ext_iff, sum_apply, mul_apply, pi.zero_apply, star_zero, row_apply,
      col_apply, mul_zero, finset.sum_const_zero, eq_self_iff_true, forall_2_true_iff], },
end

lemma pos_semidef.mul_conj_transpose_self {𝕜 n₁ n₂ : Type*} [is_R_or_C 𝕜]
  [fintype n₁] [fintype n₂] (x : matrix n₁ n₂ 𝕜) :
  (x ⬝ xᴴ).pos_semidef  :=
begin
  refine ⟨is_hermitian_mul_conj_transpose_self _, _⟩,
  simp_rw [dot_product_eq_trace, ← conj_transpose_col, conj_transpose_mul, ← matrix.mul_assoc],
  intros y,
  rw [trace_mul_cycle, ← matrix.mul_assoc, ← conj_transpose_mul, matrix.mul_assoc],
  have : (((col y)ᴴ ⬝ x)ᴴ ⬝ ((col y)ᴴ ⬝ x)).trace = ∑ (i : n₂) (j : _root_.unit), star (((col y)ᴴ ⬝ x) j i) * ((col y)ᴴ ⬝ x) j i,
  { simp_rw [← conj_transpose_apply, ← mul_apply, trace_iff], },
  simp_rw [this, map_sum],
  apply finset.sum_nonneg',
  intros,
  apply finset.sum_nonneg',
  intros,
  simp_rw [is_R_or_C.star_def, is_R_or_C.conj_mul, is_R_or_C.of_real_re],
  exact is_R_or_C.norm_sq_nonneg _,
end

end matrix
