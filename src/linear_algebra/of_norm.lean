import linear_algebra.my_ips.basic
import linear_algebra.my_ips.ips
import linear_algebra.my_ips.rank_one
import preq.is_R_or_C_le

open_locale complex_order

section ex_4

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]

lemma cs_aux {x y : E} (hy : y ≠ 0) :
  ‖x - ((inner y x : 𝕜) * (‖y‖ ^ 2)⁻¹) • y‖ ^ 2
    = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ :=
begin
  have : ((‖y‖ ^ 2 : ℝ) : 𝕜) ≠ 0,
  { rw [ne.def, is_R_or_C.of_real_eq_zero, sq_eq_zero_iff, norm_eq_zero],
    exact hy, },
  rw [← @inner_self_eq_norm_sq 𝕜],
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right,
    _root_.map_mul, inner_conj_symm, ← is_R_or_C.of_real_pow],
  simp_rw [inner_self_eq_norm_sq_to_K, star_ring_end_apply, star_inv', is_R_or_C.star_def,
    is_R_or_C.conj_of_real, mul_assoc, ← is_R_or_C.of_real_pow, inv_mul_cancel this, mul_one],
  letI : inner_product_space.core 𝕜 E := inner_product_space.to_core,
  calc is_R_or_C.re
    (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜))
      - (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner y x : 𝕜)) + (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜)))
    = is_R_or_C.re (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * inner y x)) : _
  ... = is_R_or_C.re (↑(‖x‖ ^ 2) - ‖(inner x y : 𝕜)‖ ^ 2 * ((↑(‖y‖ ^ 2))⁻¹)) : _
  ... = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ : _,
  { congr,
    ring_nf, },
  { rw [mul_rotate', ← inner_conj_symm, is_R_or_C.conj_mul, mul_comm,
      is_R_or_C.norm_sq_eq_def'],
    simp_rw [_root_.map_sub, is_R_or_C.of_real_mul_re],
    norm_cast, },
  { norm_cast, },
end

-- already exists in `mathlib`... but different proof... just for fun
example {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
  ‖(inner x y : 𝕜)‖ = ‖x‖ * ‖y‖ ↔ ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
begin
  split,
  { intros h,
    have : (inner y x : 𝕜) ≠ 0,
    { intros h',
      rw inner_eq_zero_symm at h',
      rw [h', norm_zero, eq_comm, mul_eq_zero] at h,
      simp_rw [norm_eq_zero, hx, hy, false_or] at h,
      exact h, },
    have hy' : ‖y‖ ^ 2 ≠ 0,
    { rw [ne.def, sq_eq_zero_iff, norm_eq_zero],
      exact hy, },
    rw [← sq_eq_sq (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_pow, eq_comm, ← eq_mul_inv_iff_mul_eq₀ hy',
      ← sub_eq_zero, ← cs_aux hy, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h,
    exact ⟨units.mk0 ((inner y x : 𝕜) * (((‖y‖ : 𝕜) ^ 2)⁻¹))
      (mul_ne_zero this (by {  rw [ne.def, inv_eq_zero, sq_eq_zero_iff, is_R_or_C.of_real_eq_zero,
          norm_eq_zero],
        exact hy,  })), h⟩, },
  { rintros ⟨α, rfl⟩,
    simp_rw [inner_smul_left, norm_mul, norm_smul, ← inner_self_re_eq_norm,
      inner_self_eq_norm_mul_norm, mul_assoc, is_R_or_C.norm_conj], },
end

end ex_4

open is_R_or_C
open_locale complex_conjugate

variables {𝕜 X : Type*} [is_R_or_C 𝕜] [normed_add_comm_group X] [normed_space 𝕜 X]

noncomputable def of_norm.inner_def (x y : X) : 𝕜 :=
  4⁻¹ *
  (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + I * ‖(I : 𝕜) • x + y‖ ^ 2
    - I * ‖(I : 𝕜) • x - y‖ ^ 2)

namespace of_norm

lemma re_inner_def (x y : X) :
  re (inner_def x y : 𝕜) = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) :=
begin
  calc re (inner_def x y : 𝕜)
    = re (4⁻¹ *
  (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + I * ‖(I : 𝕜) • x + y‖ ^ 2
    - I * ‖(I : 𝕜) • x - y‖ ^ 2) : 𝕜) : rfl
  ... = (4⁻¹ : ℝ) * re (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 : ℝ) : 𝕜) + (I * ((‖(I : 𝕜) • x + y‖ ^ 2
    - ‖(I : 𝕜) • x - y‖ ^ 2 : ℝ) : 𝕜))) :
  by { rw [mul_re],
    have : im (4 : 𝕜)⁻¹ = 0 := by simp,
    simp only [this, zero_mul, sub_zero, mul_sub, of_real_sub, of_real_pow],
    simp only [sub_eq_add_neg, add_assoc],
    congr,
    { calc re (4 : 𝕜)⁻¹ = re ((4 : ℝ) : 𝕜)⁻¹ :
      by { congr,
        norm_cast, }
      ... = (re ((4 : ℝ) : 𝕜))⁻¹ :
      by { simp_rw [inv_re, norm_sq_eq_def', norm_of_real],
        norm_num, }
      ... = (4 : ℝ)⁻¹ : by simp only [of_real_re], }, }
  ... = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) :
  by { rw [_root_.map_add, I_mul_re, of_real_im, neg_zero, add_zero, of_real_re], },
end

lemma im_eq_re_neg_I (x : 𝕜) :
  im x = re (- (I : 𝕜) * x) :=
begin
  simp only [neg_mul, map_neg, I_mul_re, neg_neg],
end

lemma inner_def_zero_left (x : X) :
  (inner_def 0 x : 𝕜) = 0 :=
begin
  simp only [inner_def, smul_zero, zero_add, zero_sub, norm_neg, sub_self, mul_zero],
end

theorem inner_def_I_smul_left (x y : X) :
  (inner_def ((I : 𝕜) • x) y : 𝕜) = (- I : 𝕜) * inner_def x y :=
begin
  by_cases hI : (I : 𝕜) = 0,
  { simp_rw [hI, zero_smul, inner_def_zero_left, neg_zero, zero_mul], },
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel hI],
  simp only [inner_def, smul_eq_mul, ← mul_assoc, mul_comm (-I : 𝕜) (4⁻¹)],
  simp only [mul_assoc],
  congr' 1,
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, neg_sub_left, norm_neg],
  simp only [mul_add, mul_sub],
  simp_rw [← mul_assoc, hI', one_mul, neg_mul],
  rw [sub_neg_eq_add],
  have : ‖x - y‖ = ‖-x + y‖ := by rw [← norm_neg, neg_sub', sub_eq_add_neg, neg_neg],
  rw [this, add_comm x y],
  ring_nf,
end

lemma im_inner_def_aux (x y : X) :
  im (inner_def x y : 𝕜) = re (inner_def ((I : 𝕜) • x) y : 𝕜) :=
begin
  rw [im_eq_re_neg_I, ← inner_def_I_smul_left],
end

lemma re_inner_def_symm (x y : X) :
  re (inner_def x y : 𝕜) = re (inner_def y x : 𝕜) :=
begin
  simp_rw [re_inner_def],
  rw [add_comm],
  congr' 2,
  simp only [sq_eq_sq, norm_nonneg, norm_sub_rev],
end

lemma im_inner_def_symm (x y : X) :
  im (inner_def x y : 𝕜) = - im (inner_def y x : 𝕜) :=
begin
  simp_rw [im_inner_def_aux],
  rw [re_inner_def_symm],
  by_cases (I : 𝕜) = 0,
  { simp only [re_inner_def, h, zero_smul, zero_add, add_zero, zero_sub,
      sub_zero, sub_self, norm_neg, mul_zero, neg_zero], },
  { have := norm_I_of_ne_zero h,
    simp only [re_inner_def, ← neg_mul, neg_mul_comm],
    congr' 1,
    simp only [neg_sub],
    have h₁ : ∀ a : X, ‖a‖ = ‖(I : 𝕜) • a‖ := λ a, by rw [norm_smul, norm_I_of_ne_zero h, one_mul],
    rw [h₁ (y + (I : 𝕜) • x), h₁ (y - (I : 𝕜) • x)],
    simp only [smul_add, smul_sub, smul_smul, I_mul_I_of_nonzero h, neg_one_smul],
    simp_rw [sub_eq_add_neg, neg_neg], },
end

lemma inner_def_conj (x y : X) :
  conj (inner_def x y : 𝕜) = inner_def y x :=
begin
  rw [← @re_add_im 𝕜 _ (inner_def x y)],
  simp_rw [map_add, map_mul, conj_of_real, conj_I],
  calc ↑(re (inner_def x y : 𝕜)) + ↑(im (inner_def x y : 𝕜)) * -(I : 𝕜)
    = ↑(re (inner_def y x : 𝕜)) + ↑(-im (inner_def x y : 𝕜)) * (I : 𝕜) :
  by { rw [re_inner_def_symm],
    congr' 1,
    simp, }
  ... = ↑(re (inner_def y x : 𝕜)) + ↑(im (inner_def y x : 𝕜)) * (I : 𝕜) :
  by { rw ← im_inner_def_symm, }
  ... = inner_def y x : re_add_im _,
end

section fromMathlib4
/-!
  In this section we show the addition property and scalar-multiplication property by mimicking (and copying) the `Mathlib4` code on `InnerProductSpace.ofNorm`.
-/

private theorem add_left_aux1
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  ‖x + y + z‖ * ‖x + y + z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  convert h (x + y + z) (x - z) using 4,
  all_goals { rw [two_smul], abel },
end

private theorem add_left_aux2
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  ‖x + y - z‖ * ‖x + y - z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 - ‖x + z‖ * ‖x + z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := h (x + y - z) (x + z),
  convert h₀ using 4,
  all_goals { rw [two_smul], abel },
end

private theorem add_left_aux2'
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  ‖x + y + z‖ * ‖x + y + z‖ - ‖x + y - z‖ * ‖x + y - z‖ = ‖x + z‖ * ‖x + z‖ - ‖x - z‖ * ‖x - z‖ +
    (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 :=
by rw [add_left_aux1 h, add_left_aux2 h]; ring

private theorem add_left_aux3
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
  ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ := by
begin
  apply eq_sub_of_add_eq,
  convert h (y + z) z using 4,
  all_goals { try { rw [two_smul], }, abel },
end

private theorem add_left_aux4
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
  ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ :=
begin
  apply eq_sub_of_add_eq',
  have h₀ := h (y - z) z,
  convert h₀ using 4,
  all_goals { try { rw [two_smul], }, abel, },
end

private theorem add_left_aux4'
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
  (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2
    = ‖y + z‖ * ‖y + z‖ - ‖y - z‖ * ‖y - z‖ :=
by rw [add_left_aux3 h, add_left_aux4 h]; ring

private theorem add_left_aux5
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  ‖(I : 𝕜) • (x + y) + z‖ * ‖(I : 𝕜) • (x + y) + z‖
    = (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖
      + ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖) / 2
      - ‖(I : 𝕜) • x - z‖ * ‖(I : 𝕜) • x - z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := h ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z),
  convert h₀ using 4,
  all_goals { try { simp only [two_smul, smul_add], }, abel },
end

private theorem add_left_aux6
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  ‖(I : 𝕜) • (x + y) - z‖ * ‖(I : 𝕜) • (x + y) - z‖
    = (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖
      + ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖) / 2
      - ‖(I : 𝕜) • x + z‖ * ‖(I : 𝕜) • x + z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := h ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z),
  convert h₀ using 4,
  all_goals { try { simp only [two_smul, smul_add], }, abel, },
end

private theorem add_left_aux7
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
  ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖
    = 2 * (‖(I : 𝕜) • y + z‖ * ‖(I : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) - ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := h ((I : 𝕜) • y + z) z,
  convert h₀ using 4,
  all_goals { try { simp only [two_smul, smul_add], }, abel, },
end

private theorem add_left_aux8
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
  ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖
    = 2 * (‖(I : 𝕜) • y - z‖ * ‖(I : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) - ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ :=
begin
  apply eq_sub_of_add_eq',
  have h₀ := h ((I : 𝕜) • y - z) z,
  convert h₀ using 4,
  all_goals { try { simp only [two_smul, smul_add], }, abel },
end

lemma inner_def_add_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (x y z : X) :
  (inner_def (x + y) z : 𝕜) = inner_def x z + inner_def y z :=
begin
  simp only [inner_def, ← mul_add],
  congr,
  simp only [mul_assoc, ← map_mul, add_sub_assoc, ← mul_sub, ← map_sub],
  rw [add_add_add_comm],
  simp only [← map_add, ← mul_add, pow_two, ← of_real_mul, ← of_real_sub, ← of_real_add],
  congr,
  { rw [← add_sub_assoc, add_left_aux2' h x y z, add_left_aux4' h], },
  { rw [add_sub],
    by_cases h₀ : (I : 𝕜) = 0,
    { simp only [h₀, zero_smul, zero_add, zero_sub, sub_self, norm_neg], },
    { have h₀₀ := I_mul_I_of_nonzero h₀,
      have h₀₁ := norm_I_of_ne_zero h₀,
      rw [add_left_aux5 h, add_left_aux6 h, add_left_aux7 h, add_left_aux8 h],
      simp only [map_sub, map_mul, map_add, div_eq_mul_inv],
      ring_nf, }, },
end

theorem inner_def_nsmul_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
  (n : ℕ) (x y : X) :
  inner_def ((n : 𝕜) • x) y = (n : 𝕜) * inner_def x y :=
begin
  induction n with n hd,
  { simp only [inner_def, zero_sub, nat.cast_zero, zero_mul,
      eq_self_iff_true, zero_smul, zero_add, mul_zero, sub_self, norm_neg, smul_zero], },
  { simp only [nat.cast_succ, add_smul, one_smul, add_mul, one_mul],
    rw [← hd, ← inner_def_add_left h], },
end

lemma inner_def_neg_one_smul_left (x y : X) :
  (inner_def (((-1 : ℤ) : 𝕜) • x) y : 𝕜) = - inner_def x y :=
begin
  simp only [inner_def, neg_mul_eq_neg_mul, one_mul, int.cast_one, one_smul, ring_hom.map_one, map_neg,
    int.cast_neg, neg_smul, neg_one_mul],
  rw [neg_mul_comm],
  congr' 1,
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg],
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add],
  have h₃ : ‖(I : 𝕜) • -x + y‖ = ‖(I : 𝕜) • x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add, ← smul_neg],
  have h₄ : ‖(I : 𝕜) • -x - y‖ = ‖(I : 𝕜) • x + y‖ := by rw [smul_neg, ← neg_add', norm_neg],
  rw [h₁, h₂, h₃, h₄],
  ring,
end

private theorem inner_def_zsmul_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (n : ℤ)
    (x y : X) :
    inner_def ((n : 𝕜) • x) y = (n : 𝕜) * inner_def x y :=
begin
  rw [← n.sign_mul_nat_abs],
  simp only [int.cast_of_nat, map_nat_cast, map_int_cast, int.cast_mul, map_mul, mul_smul],
  obtain hn | rfl | hn := lt_trichotomy n 0,
  { rw [int.sign_eq_neg_one_of_neg hn, inner_def_neg_one_smul_left, int.cast_coe_nat,
      inner_def_nsmul_left h (n.nat_abs)],
    simp only [int.cast_one, int.cast_neg, neg_one_mul, neg_mul, one_mul], },
  { simp [inner_def_zero_left], },
  { rw [int.sign_eq_one_of_pos hn],
    simp only [int.cast_one, one_smul, one_mul, int.cast_coe_nat, inner_def_nsmul_left h], },
end

private theorem inner_def_rat_smul_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
  (r : ℚ) (x y : X) :
  (inner_def ((r : 𝕜) • x) y : 𝕜) = (r : 𝕜) • inner_def x y :=
begin
  have : (r.denom : 𝕜) ≠ 0,
  { haveI : char_zero 𝕜 := is_R_or_C.char_zero_R_or_C,
    norm_cast,
    exact r.pos.ne', },
  rw [← r.num_div_denom, ← mul_right_inj' this, rat.cast_div],
  simp only [map_nat_cast, rat.cast_coe_nat, map_int_cast, rat.cast_coe_int, map_div₀],
  simp_rw [div_eq_mul_inv, ← smul_smul, inner_def_zsmul_left h],
  rw [← mul_assoc, mul_comm ↑(r.denom) _, mul_assoc, ← inner_def_nsmul_left h],
  simp [smul_smul, ← mul_assoc],
  rw [mul_rotate ↑(r.denom)],
  simp only [mul_assoc],
  congr' 1,
  simp only [← mul_assoc, inv_mul_cancel this, mul_inv_cancel this, one_smul, one_mul],
end

theorem _root_.continuous.inner_def {f g : ℝ → X} (hf : continuous f) (hg : continuous g) :
    continuous (λ x : ℝ, (inner_def (f x) (g x) : 𝕜)) :=
begin
  unfold inner_def,
  continuity,
end

private theorem inner_def_rsmul_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
  (r : ℝ) (x y : X) :
  inner_def ((r : 𝕜) • x) y = (r : 𝕜) * inner_def x y :=
begin
  revert r,
  rw [← function.funext_iff],
  refine rat.dense_embedding_coe_real.dense.equalizer _ _ (funext (λ _, _)),
  { exact (continuous_of_real.smul continuous_const).inner_def continuous_const, },
  { continuity, },
  { simp only [function.comp_apply, is_R_or_C.of_real_rat_cast, inner_def_rat_smul_left h],
    refl, },
end

theorem inner_def_smul_left
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
  (r : 𝕜) (x y : X) :
  inner_def (r • x) y = conj r * inner_def x y :=
begin
  rw [← re_add_im r, add_smul, inner_def_add_left h, inner_def_rsmul_left h, ← smul_smul, inner_def_rsmul_left h,
    inner_def_I_smul_left, map_add, map_mul, conj_of_real, conj_of_real, conj_I],
  ring,
end

/-!
 End of section from `Mathlib4`.
-/

end fromMathlib4

noncomputable def inner_product_spacce.of_norm
  (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
  inner_product_space 𝕜 X :=
{ inner := λ x y, inner_def x y,
  norm_sq_eq_inner := λ x, by { simp only [inner, re_inner_def, pow_two],
    specialize h x x,
    simp only [sub_self, norm_zero, zero_mul, sub_zero, add_zero] at h ⊢,
    simp only [h, ← two_mul, ← mul_assoc],
    norm_num, },
  conj_symm := λ x y, inner_def_conj y x,
  add_left := λ x y z, inner_def_add_left h _ _ _,
  smul_left := λ r x y, inner_def_smul_left h _ _ _ }

end of_norm

open_locale complex_conjugate

def is_continuous_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] (f : E → F) : Prop :=
is_linear_map 𝕜 f ∧ continuous f

def is_continuous_linear_map.mk' {𝕜 : Type*} [normed_field 𝕜] {E : Type*}
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] {f : E → F} (h : is_continuous_linear_map 𝕜 f) :
  E →L[𝕜] F :=
⟨h.1.mk' f, h.2⟩

lemma is_continuous_linear_map.coe_mk' {𝕜 : Type*} [normed_field 𝕜] {E : Type*}
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] {f : E → F} (h : is_continuous_linear_map 𝕜 f) :
  f = h.mk' :=
rfl

lemma is_bounded_linear_map_iff_is_continuous_linear_map {𝕜 E : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] (f : E → F) :
  is_bounded_linear_map 𝕜 f ↔ is_continuous_linear_map 𝕜 f :=
begin
  refine ⟨λ h, ⟨is_bounded_linear_map.to_is_linear_map h, is_bounded_linear_map.continuous h⟩, λ h, _⟩,
  let f' : E →L[𝕜] F := ⟨h.1.mk' f, h.2⟩,
  exact f'.is_bounded_linear_map,
end

private lemma linear_map.is_bounded_linear_map_iff_is_continuous {𝕜 E : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] (f : E →ₗ[𝕜] F) :
  is_bounded_linear_map 𝕜 f ↔ continuous f :=
begin
  rw [is_bounded_linear_map_iff_is_continuous_linear_map, is_continuous_linear_map],
  simp only [and_iff_right_iff_imp, f.is_linear, implies_true_iff],
end

def with_bound (𝕜 : Type*) {E : Type*} [normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] (f : E → F) : Prop :=
∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖

lemma is_bounded_linear_map.def {𝕜 E : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] {f : E → F} :
  is_bounded_linear_map 𝕜 f ↔ (is_linear_map 𝕜 f ∧ with_bound 𝕜 f) :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

lemma linear_map.with_bound_iff_is_continuous {𝕜 E : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] {f : E →ₗ[𝕜] F} :
  with_bound 𝕜 f ↔ continuous f :=
begin
  have := @is_bounded_linear_map_iff_is_continuous_linear_map 𝕜 _ _ _ _ _ _ _ f,
  simp only [is_bounded_linear_map.def, is_continuous_linear_map, and.congr_right_iff,
    f.is_linear, true_implies_iff] at this,
  exact this,
end

lemma linear_map.ker_coe_def {R E F : Type*} [semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R E] [module R F] {f : E →ₗ[R] F} :
  (f.ker : set E) = {x : E | f x = 0} := 
rfl

lemma exists_dual_vector_of_ne {X : Type*} [normed_add_comm_group X]
  [normed_space 𝕜 X] {x y : X} (h : x ≠ y) :
  ∃ f : normed_space.dual 𝕜 X, f x ≠ f y :=
begin
  rw [ne.def, ← sub_eq_zero] at h,
  obtain ⟨f, ⟨hf, hxy⟩⟩ := @exists_dual_vector 𝕜 _ X _ _ _ h,
  rw [map_sub] at hxy,
  use f,
  intros H,
  rw [H, sub_self, eq_comm, is_R_or_C.of_real_eq_zero, norm_eq_zero] at hxy,
  contradiction,
end

lemma is_linear_map_zero (R : Type*) {E F : Type*} [comm_semiring R]
  [add_comm_monoid E] [module R E] [add_comm_monoid F] [module R F] :
  is_linear_map R (0 : E → F) :=
begin
  fconstructor;
  simp only [pi.zero_apply, smul_zero, add_zero];
  intros;
  trivial,
end

lemma is_continuous_linear_map_zero {𝕜 E : Type*} [normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {F : Type*} [normed_add_comm_group F]
  [normed_space 𝕜 F] :
  is_continuous_linear_map 𝕜 (0 : E → F) :=
⟨is_linear_map_zero 𝕜, continuous_zero⟩

open_locale classical topology big_operators nnreal

lemma is_continuous_linear_map.of_inner_symmetric_fun {X : Type*} [normed_add_comm_group X] [inner_product_space 𝕜 X]
  [complete_space X] {f : X → X}
  (h : ∀ a b : X, (inner (f a) b : 𝕜) = inner a (f b)) :
  is_continuous_linear_map 𝕜 f :=
begin
  have : is_linear_map 𝕜 f :=
  { map_add := λ x y, by
    { apply @ext_inner_right 𝕜,
      intros z,
      simp_rw [h, inner_add_left, h], },
    map_smul := λ r x, by
    { apply @ext_inner_right 𝕜,
      intros z,
      simp_rw [h, inner_smul_left, h], } },
  let f' : X →ₗ[𝕜] X := is_linear_map.mk' _ this,
  have : f = f' := rfl,
  simp only [this] at *,
  clear this,
  exact ⟨f'.is_linear, linear_map.is_symmetric.continuous h⟩,
end

structure is_bilinear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G] (f : E × F → G) : Prop :=
(add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y))
(smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y))
(add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂))
(smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y))

def is_left_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  (f : E × F → G) :
  Prop :=
∀ b : F, is_linear_map 𝕜 (λ a, f (a, b))
lemma is_left_linear_map_iff {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} :
  is_left_linear_map 𝕜 f ↔ ∀ b : F, is_linear_map 𝕜 (λ a, f (a, b)) :=
iff.rfl
def is_right_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  (f : E × F → G) :
  Prop :=
∀ a : E, is_linear_map 𝕜 (λ b, f (a, b))
lemma is_right_linear_map_iff {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} :
  is_right_linear_map 𝕜 f ↔ ∀ a : E, is_linear_map 𝕜 (λ b, f (a, b)) :=
iff.rfl

lemma is_bilinear_map_iff_is_linear_map_left_right
  {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} :
  is_bilinear_map 𝕜 f ↔
    is_left_linear_map 𝕜 f ∧ is_right_linear_map 𝕜 f :=
begin
  split,
  { introsI hf,
    split,
    { intros x,
      exact ⟨λ y z, hf.add_left y z x, λ r a, hf.smul_left r a x⟩, },
    { intros x,
      exact ⟨λ y z, hf.add_right x y z, λ r a, hf.smul_right r x a⟩, } },
  { rintros ⟨h1, h2⟩,
    fconstructor,
    { intros x₁ x₂ y,
      exact (h1 y).map_add _ _, },
    { intros r x y,
      exact (h1 y).map_smul _ _, },
    { intros y x₁ x₂,
      exact (h2 y).map_add _ _, },
    { intros r x y,
      exact (h2 x).map_smul _ _, }, },
end
def is_bilinear_map.to_lm_lm {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} (hf : is_bilinear_map 𝕜 f) :
  E →ₗ[𝕜] (F →ₗ[𝕜] G) :=
{ to_fun := λ x, 
  { to_fun := λ y, f (x,y),
    map_add' := λ y z, hf.add_right x _ _,
    map_smul' := λ r y, hf.smul_right r x y, },
  map_add' := λ y z, by {
    ext,
    simp only [linear_map.add_apply],
    exact hf.add_left y z x, },
  map_smul' := λ r z, by { ext,
    simp only [linear_map.smul_apply],
    exact hf.smul_left r z x, } }
def is_lm_left_is_clm_right.to_lm_clm {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} 
  (hf₁ : ∀ y, is_linear_map 𝕜 (λ a, f (a, y)))
  (hf₂ : ∀ x, is_continuous_linear_map 𝕜 (λ a, f (x, a))) :
  E →ₗ[𝕜] (F →L[𝕜] G) :=
{ to_fun := λ x, (hf₂ x).mk',
  map_add' := λ y z, by {
    ext,
    simp only [continuous_linear_map.add_apply],
    exact (hf₁ x).map_add _ _, },
  map_smul' := λ r z, by { ext,
    exact (hf₁ x).map_smul _ _, } }

lemma is_bilinear_map.zero_left {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} (h : is_bilinear_map 𝕜 f) (y : F) :
  f (0, y) = 0 :=
begin
  simp only [is_bilinear_map_iff_is_linear_map_left_right] at h,
  exact (h.1 y).map_zero,
end
lemma is_bilinear_map.zero_right {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} (h : is_bilinear_map 𝕜 f) (x : E) :
  f (x, 0) = 0 :=
begin
  simp only [is_bilinear_map_iff_is_linear_map_left_right] at h,
  exact (h.2 x).map_zero,
end
lemma is_bilinear_map.eq_zero_add_self {𝕜 : Type*} [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
  {f : E × F → G} (h : is_bilinear_map 𝕜 f) (xy : E × F) :
  f xy = f (xy.1, 0) + f xy :=
by simp_rw [h.zero_right, zero_add]

open_locale complex_order

lemma is_continuous_linear_map.to_is_lm
  {𝕜 X Y : Type*} [normed_field 𝕜] [normed_add_comm_group X]
  [normed_add_comm_group Y]
  [normed_space 𝕜 X] [normed_space 𝕜 Y]
  [complete_space X] [complete_space Y] 
  {β : X → Y} (hf : is_continuous_linear_map 𝕜 β) :
  is_linear_map 𝕜 β :=
hf.1

lemma continuous_linear_map.op_norm_le_iff
  {𝕜 X Y : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group X]
  [normed_add_comm_group Y]
  [normed_space 𝕜 X] [normed_space 𝕜 Y]
  [complete_space X] [complete_space Y]
  (f : X →L[𝕜] Y) {r : ℝ} (hr : 0 ≤ r) :
  ‖f‖ ≤ r ↔ ∀ x, ‖f x‖ ≤ r * ‖x‖ :=
begin
  split,
  { intros hf x,
    exact f.le_of_op_norm_le hf _, },
  { intros h,
    exact f.op_norm_le_bound hr h, },
end

example --is_continuous_bilinear_map_norm_of_clm
  {𝕜 X Y Z : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group X]
  [normed_add_comm_group Y] [normed_add_comm_group Z]
  [normed_space 𝕜 X] [normed_space 𝕜 Y] [normed_space 𝕜 Z]
  [complete_space X] [complete_space Y] [complete_space Z]
  (β : X →L[𝕜] (Y →L[𝕜] Z)) :
  ∃ (M : ℝ), ∀ x y, ‖β x y‖ ≤ M * ‖x‖ * ‖y‖ :=
begin
  use ‖β‖,
  intros x y,
  apply continuous_linear_map.le_of_op_norm_le,
  exact continuous_linear_map.le_op_norm _ _,
end


