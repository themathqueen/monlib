/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.End

/-!
 # One lemma of the spectrum of a linear map

 This file just proves that the spectrum of a linear map is commutative.
-/

lemma is_unit_comm (K E : Type*) [division_ring K] [add_comm_group E] [module K E]
  [finite_dimensional K E]
  (x y : E →ₗ[K] E) : is_unit (x ∘ₗ y) ↔ is_unit (y ∘ₗ x) :=
begin
  simp_rw [← linear_map.mul_eq_comp],
  split,
  all_goals { intro h,
    rw ← nonempty_invertible_iff_is_unit at h ⊢,
    refine nonempty.intro _,
    obtain ⟨z, hz1, hz2⟩ := nonempty.some h,
    apply invertible_mul _ _,
    rw [mul_assoc, linear_map.mul_eq_one_comm, mul_assoc] at hz2,
    rw ← mul_assoc at hz1, },
  any_goals { apply invertible.mk (z * x) hz1 hz2, },
  any_goals { apply invertible.mk (z * y) hz1 hz2, },
  all_goals { rw [linear_map.mul_eq_one_comm, mul_assoc] at hz1,
    rw [mul_assoc, linear_map.mul_eq_one_comm] at hz2, },
  any_goals { exact invertible.mk (y * z) hz2 hz1, },
  any_goals { exact invertible.mk (x * z) hz2 hz1, },
end

lemma is_unit_neg {α : Type*} [monoid α] [has_distrib_neg α] (x : α) :
  is_unit (-x) ↔ is_unit (x) :=
begin
  split,
  all_goals { intros h,
    rw ← nonempty_invertible_iff_is_unit at h ⊢,
    refine nonempty.intro _,
    obtain ⟨z, hz1, hz2⟩ := nonempty.some h, },
  any_goals { rw neg_mul_comm at hz2,
    rw ← neg_mul_comm at hz1,
    exact ⟨-z, hz1, hz2⟩, },
  any_goals { rw [← neg_mul_neg] at hz2,
    rw [← neg_mul_neg] at hz1,
    exact ⟨-z, hz1, hz2⟩, },
end

lemma spectrum.comm {K E : Type*} [field K] [add_comm_group E]
  [module K E] [finite_dimensional K E] (x y : E →ₗ[K] E) :
  spectrum K (x ∘ₗ y) = spectrum K (y ∘ₗ x) :=
begin
  ext1 u,
  by_cases Hu : u = 0,
  { simp_rw [spectrum.mem_iff, Hu, algebra.algebra_map_eq_smul_one, zero_smul, zero_sub,
      is_unit_neg, is_unit_comm], },
  simp_rw [← module.End.has_eigenvalue_iff_mem_spectrum,
    ← module.End.has_eigenvector_iff_has_eigenvalue, linear_map.comp_apply],
  split; rintros ⟨v, ⟨h, hv⟩⟩,
  work_on_goal 1 { use y v, },
  work_on_goal 2 { use x v, },
  all_goals { rw [h, smul_hom_class.map_smul, eq_self_iff_true, true_and],
    intros H,
    rw [H, map_zero, eq_comm, smul_eq_zero] at h,
    simp_rw [Hu, hv, false_or] at h,
    exact h, },
end
