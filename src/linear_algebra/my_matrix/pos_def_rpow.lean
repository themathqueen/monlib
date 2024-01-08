/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.pos_eq_linear_map_is_positive
import linear_algebra.inner_aut

/-!
 # The real-power of a positive definite matrix

 This file defines the real-power of a positive definite matrix. In particular, given a positive definite matrix `x` and real number `r`, we get `pos_def.rpow` as the matrix `eigenvector_matrix * (coe ∘ diagonal (eigenvalues ^ r)) * eigenvector_matrix⁻¹`.

 It also proves some basic obvious properties of `pos_def.rpow` such as `pos_def.rpow_mul_rpow` and `pos_def.rpow_zero`.
-/

namespace matrix

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]

open_locale matrix big_operators

noncomputable def pos_def.rpow [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def)
  (r : ℝ) :
  matrix n n 𝕜 :=
inner_aut ⟨hQ.1.eigenvector_matrix, hQ.1.eigenvector_matrix_mem_unitary_group⟩
  (coe ∘ diagonal (hQ.1.eigenvalues ^ r))

lemma pos_def.rpow_mul_rpow [decidable_eq 𝕜] (r₁ r₂ : ℝ) {Q : matrix n n 𝕜} (hQ : Q.pos_def) :
  hQ.rpow r₁ ⬝ hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
begin
  simp_rw [matrix.pos_def.rpow, ← inner_aut.map_mul],
  have : (coe ∘ diagonal (hQ.1.eigenvalues ^ r₁) : matrix n n 𝕜) ⬝ (coe ∘ diagonal (hQ.1.eigenvalues ^ r₂) : matrix n n 𝕜)
    = (coe ∘ (diagonal (hQ.1.eigenvalues ^ r₁) ⬝ diagonal (hQ.1.eigenvalues ^ r₂)) : matrix n n 𝕜),
  { ext1, ext1, simp_rw [mul_apply, function.comp_apply, diagonal_mul_diagonal, diagonal],
    have : ∀ (i j : n) (v : n → ℝ),
        (↑(of (λ (i j : n), ite (i = j) (v i) 0) i : n → ℝ) : n → 𝕜) j
      = ↑(of (λ (i j : n), ite (i = j) (v i) 0) i j) := λ _ _ _, rfl,
    simp_rw [this, of_apply, ite_cast, is_R_or_C.of_real_zero, mul_ite, mul_zero,
      ite_mul, zero_mul, finset.sum_ite_eq', finset.mem_univ, if_true, ← is_R_or_C.of_real_mul],
    by_cases x = x_1,
    { simp_rw h, },
    { simp_rw [h, if_false], }, },
  simp_rw [this, diagonal_mul_diagonal, pi.pow_apply, ← real.rpow_add (hQ.pos_eigenvalues _),
    ← pi.pow_apply],
end

lemma pos_def.rpow_one_eq_self [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def) :
  hQ.rpow 1 = Q :=
begin
  simp_rw [pos_def.rpow],
  nth_rewrite_rhs 0 hQ.1.spectral_theorem',
  congr,
  simp_rw coe_diagonal_eq_diagonal_coe,
  congr,
  ext1,
  rw [pi.pow_apply, real.rpow_one],
end

lemma pos_def.rpow_neg_one_eq_inv_self [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def) :
  hQ.rpow (-(1)) = Q⁻¹ :=
begin
  simp_rw [matrix.pos_def.rpow],
  nth_rewrite_rhs 0 hQ.1.spectral_theorem',
  simp_rw [← coe_diagonal_eq_diagonal_coe, inner_aut.map_inv],
  have : (diagonal (coe ∘ hQ.1.eigenvalues) : matrix n n 𝕜)⁻¹
    = diagonal (coe ∘ hQ.1.eigenvalues)⁻¹,
  { apply inv_eq_left_inv,
    simp_rw [diagonal_mul_diagonal, pi.inv_apply, function.comp_apply,
      ← is_R_or_C.of_real_inv, ← is_R_or_C.of_real_mul, inv_mul_cancel
        (norm_num.ne_zero_of_pos _ (hQ.pos_eigenvalues _)), is_R_or_C.of_real_one,
      diagonal_one], },
  simp_rw [this],
  congr,
  ext1,
  simp_rw [pi.inv_apply, function.comp_apply, pi.pow_apply, real.rpow_neg_one,
    is_R_or_C.of_real_inv],
end

lemma pos_def.rpow_zero [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def) :
  hQ.rpow 0 = 1 :=
begin
  simp_rw [matrix.pos_def.rpow, pi.pow_def, real.rpow_zero, diagonal_one],
  have : (coe ∘ (1 : matrix n n ℝ) : matrix n n 𝕜) = (1 : matrix n n 𝕜),
  { ext1,
    simp_rw [function.comp_apply],
    have : (↑((1 : matrix n n ℝ) i) : n → 𝕜) j = ↑((1 : matrix n n ℝ) i j) := rfl,
    simp_rw [this, one_apply, ite_cast, is_R_or_C.of_real_zero, is_R_or_C.of_real_one], },
  rw [this, inner_aut_apply_one],
end

lemma pos_def.rpow.is_pos_def [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def) (r : ℝ) :
  (hQ.rpow r).pos_def :=
begin
  rw [matrix.pos_def.rpow, pos_def.inner_aut, ← coe_diagonal_eq_diagonal_coe,
    pos_def.diagonal],
  simp only [function.comp_apply, is_R_or_C.of_real_re, eq_self_iff_true, and_true,
    pi.pow_apply],
  intro i,
  have := pos_def.pos_eigenvalues hQ i,
  apply real.rpow_pos_of_pos this,
end

lemma pos_def.rpow.is_hermitian [decidable_eq 𝕜] {Q : matrix n n 𝕜} (hQ : Q.pos_def) (r : ℝ) :
  (hQ.rpow r).is_hermitian :=
(pos_def.rpow.is_pos_def hQ r).1

lemma pos_def.inv {𝕜 n : Type*} [fintype n] [is_R_or_C 𝕜]
  {Q : matrix n n 𝕜} [decidable_eq 𝕜] [decidable_eq n] (hQ : Q.pos_def) :
  (Q⁻¹).pos_def :=
begin
  rw [← matrix.pos_def.rpow_neg_one_eq_inv_self hQ, matrix.pos_def.rpow, pos_def.inner_aut,
    ← coe_diagonal_eq_diagonal_coe, pi.pow_def],
  split,
  { simp_rw [is_hermitian, diagonal_conj_transpose, pi.star_def,
      is_R_or_C.star_def, function.comp_apply, is_R_or_C.conj_of_real], },
  { simp_rw [dot_product, mul_vec, dot_product, diagonal, of_apply,
      ite_mul, zero_mul, function.comp_apply, finset.sum_ite_eq, finset.mem_univ,
      if_true, pi.star_apply, mul_comm, ← mul_assoc, is_R_or_C.star_def,
      is_R_or_C.conj_mul, ← is_R_or_C.of_real_mul, map_sum, is_R_or_C.of_real_re],
    intros x hx,
    apply finset.sum_pos',
    { intros,
      exact mul_nonneg (is_R_or_C.norm_sq_nonneg _) (real.rpow_nonneg_of_nonneg (le_of_lt (pos_def.pos_eigenvalues hQ i)) _), },
    { simp_rw [ne.def, function.funext_iff, pi.zero_apply, not_forall] at hx,
      cases hx with i hi,
      exact ⟨i, finset.mem_univ _,
        mul_pos (is_R_or_C.norm_sq_pos.mpr hi)
          (real.rpow_pos_of_pos (hQ.pos_eigenvalues _) _)⟩, }, },
end

lemma pos_def.rpow_ne_zero [nonempty n] {Q : matrix n n ℂ} (hQ : Q.pos_def) {r : ℝ} :
  hQ.rpow r ≠ 0 :=
begin
  simp_rw [matrix.pos_def.rpow, ne.def, inner_aut_eq_iff,
    inner_aut_apply_zero, ← coe_diagonal_eq_diagonal_coe,
    ← matrix.ext_iff, diagonal, dmatrix.zero_apply, of_apply, ite_eq_right_iff,
    function.comp_apply, is_R_or_C.of_real_eq_zero, pi.pow_apply,
    real.rpow_eq_zero_iff_of_nonneg (le_of_lt (hQ.pos_eigenvalues _)),
    norm_num.ne_zero_of_pos _ (hQ.pos_eigenvalues _), false_and, imp_false,
    not_forall, not_not, exists_eq', exists_const],
end

end matrix
