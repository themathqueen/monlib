/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.star.basic
import algebra.module.linear_map
import linear_algebra.tensor_product

/-!
 # Some stuff on ites

 Some lemmas about `ite` and `coe` for `star` and `tensor_product`.
-/

@[simp] lemma star_ite {α : Type*} [has_involutive_star α] (P : Prop) [decidable P] (a b : α) :
  star (ite P a b) = ite P (star a) (star b) :=
begin
  by_cases h : a = b,
  { simp_rw [h, if_t_t], },
  { have : ¬ star a = star b,
    { apply (star_injective).ne_iff.mp,
      rw [star_star a, star_star b],
      exact h, },
    by_cases h' : P,
    { simp_rw [(ne.ite_eq_left_iff h).mpr h',
               (ne.ite_eq_left_iff this).mpr h'], },
    { simp_rw [(ne.ite_eq_right_iff h).mpr h',
               (ne.ite_eq_right_iff this).mpr h'], }, },
end

lemma coe_ite {α β : Type*} [has_coe α β] (P : Prop) [decidable P] (a b : α) :
  (↑(ite P a b) : β) = ite P (a : β) (b : β) :=
begin
  by_cases h : a = b,
  { simp_rw [h, if_t_t], },
  { by_cases h' : P,
    { rw (ne.ite_eq_left_iff h).mpr h',
      symmetry,
      rw ite_eq_left_iff,
      intros g,
      contradiction, },
    { rw (ne.ite_eq_right_iff h).mpr h',
      symmetry,
      rw ite_eq_right_iff,
      intros g,
      contradiction, }, },
end

lemma ite_apply_lm {R A B : Type*} [semiring R] [add_comm_monoid A]
  [add_comm_monoid B] [module R A] [module R B]
  (f g : A →ₗ[R] B) (x : A) (P : Prop) [decidable P] :
  (if P then f else g : A →ₗ[R] B) x = if P then (f x) else (g x) :=
begin
  by_cases P,
  { simp only [h, if_true], },
  { simp only [h, if_false], },
end

local notation f ` ⊗ₘ ` g := tensor_product.map f g
open_locale tensor_product

lemma tensor_product.ite_map {R M₁ M₂ M₃ M₄ : Type*} [comm_semiring R]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
  [module R M₁] [module R M₂] [module R M₃] [module R M₄]
  (f₁ f₂ : M₁ →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (P : Prop) [decidable P] :
  ((ite P f₁ f₂) ⊗ₘ g) = (ite P (f₁ ⊗ₘ g) (f₂ ⊗ₘ g) : M₁ ⊗[R] M₃ →ₗ[R] M₂ ⊗[R] M₄) :=
by split_ifs; simp
