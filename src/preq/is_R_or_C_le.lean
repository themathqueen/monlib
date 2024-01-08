/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import data.is_R_or_C.basic

/-!
 # Strictly ordered field structure on `𝕜`

 This file defines the following structures on `𝕜`.
-/

namespace is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜]

protected def partial_order : partial_order 𝕜 :=
{ le := λ z w, re z ≤ re w ∧ im z = im w,
  lt := λ z w, re z < re w ∧ im z = im w,
  lt_iff_le_not_le := λ z w, by { dsimp, rw lt_iff_le_not_le, tauto },
  le_refl := λ x, ⟨le_rfl, rfl⟩,
  le_trans := λ x y z h₁ h₂, ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
  le_antisymm := λ z w h₁ h₂, ext (h₁.1.antisymm h₂.1) h₁.2 }

localized "attribute [instance] is_R_or_C.partial_order" in complex_order

lemma le_def {z w : 𝕜} : z ≤ w ↔ re z ≤ re w ∧ im z = im w := iff.rfl
lemma lt_def {z w : 𝕜} : z < w ↔ re z < re w ∧ im z = im w := iff.rfl

lemma nonneg_def {x : 𝕜} :
  0 ≤ x ↔ 0 ≤ re x ∧ im x = 0 :=
by simp only [le_def, map_zero, one_im, one_re, iff_self, eq_comm]
lemma pos_def {x : 𝕜} :
  0 < x ↔ 0 < re x ∧ im x = 0 :=
by simp only [lt_def, map_zero, one_im, one_re, iff_self, eq_comm]
lemma nonpos_def {x : 𝕜} :
  x ≤ 0 ↔ re x ≤ 0 ∧ im x = 0 :=
by simp only [le_def, map_zero, one_im, one_re, iff_self, eq_comm]
lemma neg_def {x : 𝕜} :
  x < 0 ↔ re x < 0 ∧ im x = 0 :=
by simp only [lt_def, map_zero, one_im, one_re, iff_self, eq_comm]

lemma nonneg_def' {x : 𝕜} :
  0 ≤ x ↔ (re x : 𝕜) = x ∧ 0 ≤ re x :=
by simp_rw [nonneg_def, ← conj_eq_iff_re, conj_eq_iff_im, and_comm]

@[simp, norm_cast] lemma real_le_real {x y : ℝ} : (x : 𝕜) ≤ (y : 𝕜) ↔ x ≤ y := by simp [le_def]

@[simp, norm_cast] lemma real_lt_real {x y : ℝ} : (x : 𝕜) < (y : 𝕜) ↔ x < y := by simp [lt_def]

@[simp, norm_cast] lemma zero_le_real {x : ℝ} : 0 ≤ (x : 𝕜) ↔ 0 ≤ x :=
by simp_rw [nonneg_def, of_real_im, eq_self_iff_true, and_true, of_real_re]

@[simp, norm_cast] lemma zero_lt_real {x : ℝ} : 0 < (x : 𝕜) ↔ 0 < x :=
by simp_rw [pos_def, of_real_im, eq_self_iff_true, and_true, of_real_re]

lemma not_le_iff {z w : 𝕜} : ¬(z ≤ w) ↔ re w < re z ∨ im z ≠ im w :=
by rw [le_def, not_and_distrib, not_le]

lemma not_lt_iff {z w : 𝕜} : ¬(z < w) ↔ re w ≤ re z ∨ im z ≠ im w :=
by rw [lt_def, not_and_distrib, not_lt]

lemma not_le_zero_iff {z : 𝕜} : ¬z ≤ 0 ↔ 0 < re z ∨ im z ≠ 0 :=
by simp only [not_le_iff, map_zero]
lemma not_lt_zero_iff {z : 𝕜} : ¬z < 0 ↔ 0 ≤ re z ∨ im z ≠ 0 :=
by simp only [not_lt_iff, map_zero]

lemma eq_re_of_real_le {r : ℝ} {z : 𝕜} (hz : (r : 𝕜) ≤ z) : z = re z :=
by { rw is_R_or_C.ext_iff,
  exact ⟨by simp only [of_real_re],
    by simp only [←(is_R_or_C.le_def.1 hz).2, map_zero, is_R_or_C.of_real_im]⟩, }

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `𝕜` is a strictly ordered ring.
-/
protected def strict_ordered_comm_ring : strict_ordered_comm_ring 𝕜 :=
{ zero_le_one := by { rw [nonneg_def], simp only [one_re, zero_le_one, one_im, eq_self_iff_true, and_self] },
  add_le_add_left := λ w z h y, by { simp only [le_def, map_add],
    exact ⟨add_le_add_left h.1 _, congr_arg2 _ rfl (le_def.mp h).2⟩, },
  mul_pos := λ z w hz hw,
    by { simp [lt_def, mul_re, mul_im, ← hz.2, ← hw.2, mul_pos (pos_def.mp hz).1 (pos_def.mp hw).1], },
  ..is_R_or_C.partial_order, ..field.to_comm_ring 𝕜, ..is_domain.to_nontrivial 𝕜 }

localized "attribute [instance] is_R_or_C.strict_ordered_comm_ring" in complex_order

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `𝕜` is a star ordered ring.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)
-/
protected def star_ordered_ring : star_ordered_ring 𝕜 :=
star_ordered_ring.of_nonneg_iff' (λ _ _, add_le_add_left) $ λ r,
begin
  refine ⟨λ hr, ⟨real.sqrt (re r), _⟩, λ h, _⟩,
  { have h₁ : 0 ≤ re r := by { rw [nonneg_def] at hr, exact hr.1 },
    have h₂ : im r = 0 := by { rw [nonneg_def] at hr, exact hr.2 },
    rw ext_iff,
    split,
    { simp only [of_real_im, star_def, of_real_re, sub_zero, conj_re, mul_re, mul_zero,
                 ←real.sqrt_mul h₁ (re r), real.sqrt_mul_self h₁] },
    { simp only [h₂, add_zero, of_real_im, star_def, zero_mul, conj_im,
                 mul_im, mul_zero, neg_zero] } },
  { obtain ⟨s, rfl⟩ := h,
    simp only [conj_mul, norm_sq_nonneg, zero_le_real, star_def], },
end

localized "attribute [instance] is_R_or_C.star_ordered_ring" in complex_order

end is_R_or_C
