/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.algebra.pi
import linear_algebra.projective_space.basic
import preq.ites

/-!

# Direct sum from _ to _

 This file includes the definition of `direct_sum_from_to` which is a linear map from `M i` to `M j`.

-/

def direct_sum_from_to {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] (i j : ι₁) :
  (M₁ i) →ₗ[R] (M₁ j) :=
(linear_map.proj j) ∘ₗ (linear_map.single i)

lemma direct_sum_from_to_apply_same {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] (i : ι₁) :
  direct_sum_from_to i i = (1 : M₁ i →ₗ[R] M₁ i) :=
begin
  ext1 x,
  simp only [direct_sum_from_to, linear_map.comp_apply, linear_map.coe_single, pi.single,
    linear_map.coe_proj, function.eval_apply, function.update_apply, pi.zero_apply,
    ite_apply_lm, linear_map.zero_apply, linear_map.one_apply],
  simp,
end
lemma direct_sum_from_to_apply_ne_same {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₁ : ι₁), module R (M₁ i₁)] {i j : ι₁} (h : j ≠ i) :
  direct_sum_from_to i j = (0 : M₁ i →ₗ[R] M₁ j) :=
begin
  ext1 x,
  simp only [direct_sum_from_to, linear_map.comp_apply, linear_map.coe_single, pi.single,
    linear_map.coe_proj, function.eval_apply, function.update_apply, pi.zero_apply,
    ite_apply_lm, linear_map.zero_apply, linear_map.one_apply],
  simp [h],
end