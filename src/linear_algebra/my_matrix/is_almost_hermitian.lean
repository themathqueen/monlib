/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.matrix.block
import linear_algebra.my_matrix.basic

/-!
 # Almost Hermitian Matrices

 This file contains the definition and some basic results about almost Hermitian matrices.

 We say a matrix `x` is `is_almost_hermitian` if there exists some scalar `α ∈ ℂ`.
-/

namespace matrix

variables {𝕜 n : Type*}

open_locale matrix

/-- a matrix $x \in M_n(\mathbb{k})$ is ``almost Hermitian'' if there exists some $\alpha\in\mathbb{k}$
  and $y\in M_n(\mathbb{k})$ such that $\alpha y = x$ and $y$ is Hermitian -/
def is_almost_hermitian [has_star 𝕜] [has_smul 𝕜 (matrix n n 𝕜)] (x : matrix n n 𝕜) :
  Prop :=
∃ (α : 𝕜) (y : matrix n n 𝕜), α • y = x ∧ y.is_hermitian

open_locale kronecker

open complex

open_locale complex_conjugate

/-- $x\in M_n(\mathbb{C})$ is almost Hermitian if and only if $x \otimes_k \bar{x}$ is Hermitian -/
lemma is_almost_hermitian_iff (x : matrix n n ℂ) :
  x.is_almost_hermitian ↔ (x ⊗ₖ xᴴᵀ).is_hermitian :=
begin
  split,
  { rintros ⟨α, y, ⟨rfl, h⟩⟩,
    simp_rw [is_hermitian, kronecker_conj_transpose, conj_conj_transpose,
      conj_smul, transpose_smul, conj_transpose_smul, h.eq, kronecker_smul,
      smul_kronecker, smul_smul, mul_comm, h.conj], },
  { intros h,
    simp_rw [is_hermitian, ← matrix.ext_iff, conj_transpose_apply, kronecker_map,
      of_apply, conj_apply, star_mul', star_star, mul_comm _ (star _)] at h,
    have : ∀ i j : n, x i j = 0 ↔ x j i = 0,
    { intros i j,
      specialize h (i,i) (j,j),
      simp_rw [is_R_or_C.star_def, is_R_or_C.conj_mul] at h,
      norm_cast at h,
      split; intros H,
      { rw [H, map_zero, is_R_or_C.norm_sq_eq_zero] at h,
        exact h, },
      { rw [H, map_zero, eq_comm, is_R_or_C.norm_sq_eq_zero] at h,
        exact h, }, },
    have this1 : ∀ i j : n, x i j = 0 ↔ xᴴ i j = 0,
    { simp_rw [conj_transpose_apply, star_eq_zero, this, iff_self, forall_2_true_iff], },
    by_cases h' : x = 0,
    { rw h',
      use 0, use 0,
      simp_rw [zero_smul, is_hermitian_zero, eq_self_iff_true, true_and], },

    have hα_pre : ∀ i j k l : n, x i j ≠ 0 → x k l ≠ 0 → x i j / star (x j i) = x k l / star (x l k),
    { intros m₁ m₂ m₃ m₄ hx₁ hx₂,
      rw [ne.def, this] at hx₁ hx₂,
      simp_rw [div_eq_div_iff (star_ne_zero.mpr hx₁) (star_ne_zero.mpr hx₂), mul_comm _ (star _),
        is_R_or_C.star_def],
      exact h (_,_) (_,_), },

    have nonzero_ : ∃ i j : n, x i j ≠ 0,
    { simp_rw [ne.def, ← not_forall, eq_zero],
      exact h', },
    have nonzero_' := nonzero_,
    rcases nonzero_ with ⟨i, k, hik⟩,

    let α := x i k / star (x k i),
    have hα' : α ≠ 0,
    { simp_rw [α, div_ne_zero_iff, star_ne_zero, ne.def, this k i],
      exact ⟨hik, hik⟩, },
    have Hα : α⁻¹ = conj α,
    { simp_rw [α, ← is_R_or_C.star_def, star_div', star_star, inv_div, is_R_or_C.star_def,
        div_eq_div_iff hik ((not_iff_not.mpr (this i k)).mp hik), ← is_R_or_C.star_def,
        h (k,k) (i,i)], },
    have conj_ : ∀ α : ℂ, is_R_or_C.norm_sq α = is_R_or_C.re (conj α * α) := λ α,
    by { simp_rw [is_R_or_C.conj_mul, is_R_or_C.of_real_re], },
    have Hα' : real.sqrt (is_R_or_C.norm_sq α) = 1,
    { simp_rw [real.sqrt_eq_iff_sq_eq (is_R_or_C.norm_sq_nonneg _) zero_le_one,
        one_pow, conj_, ← Hα, inv_mul_cancel hα', is_R_or_C.one_re], },

    have another_hα : ∀ p q : n, x p q ≠ 0 → x p q = α * conj (x q p),
    { intros p q hpq,
      simp_rw [α, div_mul_eq_mul_div, mul_comm (x i k), ← is_R_or_C.star_def,
        h (p,_) (_,_), ← div_mul_eq_mul_div, ← star_div',
        div_self ((not_iff_not.mpr (this i k)).mp hik), star_one, one_mul], },

    have : ∃ β : ℂ, β ^ 2 = α,
    { existsi α ^ (↑2)⁻¹,
      exact complex.cpow_nat_inv_pow α two_ne_zero, },
    cases this with β hβ,
    have hβ' : β ≠ 0,
    { rw [ne.def, ← sq_eq_zero_iff, hβ],
      exact hα', },
    have hβ'' : β⁻¹ = conj β,
    { rw [← mul_left_inj' hβ', inv_mul_cancel hβ', ← complex.norm_sq_eq_conj_mul_self],
      norm_cast,
      simp_rw [complex.norm_sq_eq_abs, ← complex.abs_pow, hβ],
      exact Hα'.symm, },
    have hαβ : β * α⁻¹ = β⁻¹,
    { rw [← hβ, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel hβ', one_mul], },

    use β,
    use β⁻¹ • x,

    simp_rw [is_hermitian, conj_transpose_smul, ← matrix.ext_iff, pi.smul_apply,
      conj_transpose_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel hβ', one_mul,
      eq_self_iff_true, forall_2_true_iff, true_and, hβ'', ← complex.star_def, star_star],
    { intros p q,
      by_cases H : x p q = 0,
      { simp_rw [H, (this p q).mp H, star_zero, mul_zero], },
      { calc β * star (x q p) = β * star (α * star (x p q)) : _
          ... = β * α⁻¹ * x p q : _
          ... = star β * x p q : _,
        { rw [another_hα _ _ ((not_iff_not.mpr (this p q)).mp H), complex.star_def], },
        { rw [star_mul', star_star, mul_comm (star _) (x p q), mul_assoc, mul_comm _ (star _),
            Hα, ← complex.star_def], },
        { simp_rw [hαβ, hβ'', ← complex.star_def], }, }, }, },
end

/-- 0 is almost Hermitian -/
lemma is_almost_hermitian_zero [semiring 𝕜] [star_ring 𝕜] :
  (0 : matrix n n 𝕜).is_almost_hermitian :=
begin
  use 0, use 0,
  simp_rw [is_hermitian_zero, zero_smul, and_true],
end

/-- if $x$ is almost Hermitian, then it is also normal -/
lemma almost_hermitian.is_star_normal [fintype n] [comm_semiring 𝕜] [star_ring 𝕜]
  {M : matrix n n 𝕜} (hM : M.is_almost_hermitian) :
  is_star_normal M :=
begin
  obtain ⟨α, N, ⟨rfl, hN⟩⟩ := hM,
  apply is_star_normal.mk,
  simp_rw [commute, semiconj_by, star_smul, smul_mul_smul, star_eq_conj_transpose,
    hN.eq, mul_comm],
end

/-- $x$ is almost Hermitian if and only if $\beta \cdot x$ is almost Hermitian for any $\beta$ -/
lemma almost_hermitian_iff_smul [comm_semiring 𝕜] [star_ring 𝕜] {M : matrix n n 𝕜} :
  M.is_almost_hermitian ↔ ∀ β : 𝕜, (β • M).is_almost_hermitian :=
begin
  split,
  { rintros ⟨α, N, ⟨rfl, hN⟩⟩ β,
    use β * α,
    use N,
    simp_rw [smul_smul, eq_self_iff_true, true_and, hN], },
  { intros h,
    specialize h (1 : 𝕜),
    simp_rw [one_smul] at h,
    exact h, },
end

def is_diagonal {R n : Type*} [has_zero R] (A : matrix n n R) : Prop :=
∀ i j : n, i ≠ j → A i j = 0

lemma is_diagonal_eq {R : Type*} [has_zero R] [decidable_eq n] (A : matrix n n R) :
  A.is_diagonal ↔ diagonal A.diag = A :=
begin
  simp_rw [← ext_iff, is_diagonal, diagonal],
  split,
  { intros h i j,
    by_cases H : i = j,
    { simp_rw [H, of_apply, eq_self_iff_true, if_true, diag], },
    { rw [of_apply, h _ _ H, ite_eq_right_iff],
      intros,
      contradiction, }, },
  { rintros h i j hij,
    specialize h i j,
    simp_rw [of_apply, hij, if_false] at h,
    exact h.symm, },
end

open_locale big_operators
/-- an almost Hermitian matrix is upper-triangular if and only if it is diagonal -/
lemma is_almost_hermitian.upper_triangular_iff_diagonal [field 𝕜] [star_ring 𝕜]
  [linear_order n] {M : matrix n n 𝕜} (hM : M.is_almost_hermitian) :
  M.block_triangular id ↔ M.is_diagonal :=
begin
  rcases hM with ⟨α, N, ⟨rfl, hN⟩⟩,
  simp_rw [block_triangular, function.id_def, pi.smul_apply],
  split,
  { intros h i j hij,
    by_cases H : j < i,
    { exact h H, },
    { simp_rw [not_lt, le_iff_eq_or_lt, hij, false_or] at H,
      specialize h H,
      by_cases Hα : α = 0,
      { simp_rw [Hα, zero_smul, pi.zero_apply], },
      { simp_rw [smul_eq_zero, Hα, false_or] at h,
        rw ← hN.eq,
        simp_rw [pi.smul_apply, conj_transpose_apply, h, star_zero, smul_zero], }, }, },
  { intros h i j hij,
    exact h i j (ne_of_lt hij).symm, },
end

lemma is_hermitian.is_almost_hermitian [semiring 𝕜] [has_star 𝕜] {x : matrix n n 𝕜} (hx : x.is_hermitian) :
  x.is_almost_hermitian :=
begin
  use 1,
  use x,
  rw [one_smul],
  exact ⟨rfl, hx⟩,
end

end matrix
