/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import logic.basic
import algebra.group.defs
import group_theory.group_action.defs
import algebra.star.basic
import linear_algebra.tensor_product

/-!
 # Some stuff on dites
-/

lemma dite_add_dite {α : Type*} [has_add α] (P : Prop) [decidable P] (a b : P → α)
  (c d : ¬ P → α) :
  dite P (λ x, a x) (λ x, c x) + dite P (λ x, b x) (λ x, d x)
    = dite P (λ x, a x + b x) (λ x, c x + d x) :=
begin
  rw eq_comm,
  simp only [dite_eq_iff'],
  split,
  { intros h,
    simp only [h, dif_pos], },
  { intros h,
    simp only [h, dif_neg, not_false_iff], },
end
lemma smul_dite {α : Type*} (P : Prop) [decidable P] (a : P → α)
  (c : ¬ P → α) {β : Type*} (r : β) [has_smul β α] :
  r • dite P (λ x, a x) (λ x, c x)
    = dite P (λ x, r • a x) (λ x, r • c x) :=
begin
  rw eq_comm,
  simp only [dite_eq_iff'],
  split,
  { intros h,
    simp only [h, dif_pos], },
  { intros h,
    simp only [h, dif_neg, not_false_iff], },
end
lemma mul_dite {α : Type*} [has_mul α] (P : Prop) [decidable P] (a : α)
  (b : P → α) (c : ¬ P → α) :
  a * dite P (λ x, b x) (λ x, c x) = dite P (λ x, a * b x) (λ x, a * c x) :=
begin
  rw eq_comm,
  simp only [dite_eq_iff'],
  split,
  { intros h,
    simp only [h, dif_pos], },
  { intros h,
    simp only [h, dif_neg, not_false_iff], },
end
lemma dite_mul {α : Type*} [has_mul α] (P : Prop) [decidable P] (a : α)
  (b : P → α) (c : ¬ P → α) :
  dite P (λ x, b x) (λ x, c x) * a = dite P (λ x, b x * a) (λ x, c x * a) :=
begin
  rw eq_comm,
  simp only [dite_eq_iff'],
  split,
  { intros h,
    simp only [h, dif_pos], },
  { intros h,
    simp only [h, dif_neg, not_false_iff], },
end

lemma dite_boole_add {α : Type*} [add_zero_class α] (P : Prop) [decidable P] (a b : P → α) :
  dite P (λ x, a x + b x) (λ x, 0)
    = dite P (λ x, a x) (λ x, 0) + dite P (λ x, b x) (λ x, 0) :=
by rw [dite_add_dite, add_zero]

lemma dite_boole_smul {α β : Type*} [has_zero α]
  [smul_zero_class β α] (P : Prop) [decidable P] (a : P → α) (r : β) :
  dite P (λ x, r • a x) (λ x, 0)
    = r • dite P (λ x, a x) (λ x, 0) :=
by rw [smul_dite, smul_zero]

lemma star_dite (P : Prop) [decidable P] {α : Type*} [has_involutive_star α]
  (a : P → α) (b : ¬ P → α) :
  star (dite P (λ i, a i) (λ i, b i)) = dite P (λ i, star (a i)) (λ i, star (b i)) :=
begin
  rw [eq_comm, dite_eq_iff'],
  split,
  { intros h,
    simp only [h, dif_pos], },
  { intros h,
    simp only [h, dif_neg, not_false_iff], },
end

lemma dite_tmul {R N₁ N₂ : Type*} [comm_semiring R]
  [add_comm_group N₁] [add_comm_group N₂] [module R N₁] [module R N₂]
  (P : Prop) [decidable P] (x₁ : P → N₁) (x₂ : N₂) :
  (dite P (λ h, x₁ h) (λ h, 0)) ⊗ₜ[R] x₂ = dite P (λ h, x₁ h ⊗ₜ[R] x₂) (λ h, 0) :=
by { split_ifs; simp }

lemma tmul_dite {R N₁ N₂ : Type*} [comm_semiring R]
  [add_comm_group N₁] [add_comm_group N₂] [module R N₁] [module R N₂]
  (P : Prop) [decidable P] (x₁ : N₁) (x₂ : P → N₂) :
  x₁ ⊗ₜ[R] (dite P (λ h, x₂ h) (λ h, 0)) = dite P (λ h, x₁ ⊗ₜ[R] x₂ h) (λ h, 0) :=
by { split_ifs; simp }

lemma linear_map.apply_dite {R H₁ H₂ : Type*} [semiring R] [add_comm_monoid H₁]
  [add_comm_monoid H₂] [module R H₁] [module R H₂] (f : H₁ →ₗ[R] H₂) (P : Prop) [decidable P]
  (a : P → H₁) (b : ¬ P → H₁) :
  f (dite P (λ h, a h) (λ h, b h)) = dite P (λ h, f (a h)) (λ h, f (b h)) :=
begin
  split_ifs;
  simp,
end
