/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.star.order
import group_theory.subgroup.basic
import data.fintype.pi
import algebra.star.pi
import data.complex.basic

/-!
  # pi.star_ordered_ring

  This file contains the definition of `pi.star_ordered_ring`.
-/

lemma add_submonoid.mem_pi {ι : Type*} [B : ι → Type*] [Π i, add_zero_class (B i)]
  (x : Π i, add_submonoid (B i)) (y : Π i, B i) :
  y ∈ add_submonoid.pi set.univ x ↔ ∀ i, y i ∈ x i :=
begin
  simp_rw [add_submonoid.pi, add_submonoid.mem_mk, set.mem_univ_pi, add_submonoid.mem_carrier],
end

def set.of_pi {ι : Type*} {B : ι → Type*} [decidable_eq ι]
  [Π i, has_zero (B i)] (s : set (Π i, B i)) :
  Π i, set (B i) :=
λ i x, pi.single i x ∈ s

lemma set.pi_of_pi {ι : Type*} {B : ι → Type*} [decidable_eq ι]
  [Π i, add_zero_class (B i)] {s : Π i, set (B i)}
  (h : ∀ i, s i 0)
  : (set.univ.pi s).of_pi = s :=
begin
  ext i x,
  simp_rw [set.of_pi, set.mem_univ_pi, set.mem_def],
  split,
  { intros hi,
    specialize hi i,
    rw [pi.single_eq_same] at hi,
    exact hi, },
  { intros hx j,
    by_cases hj : j = i,
    { rw hj,
      rw [pi.single_eq_same],
      exact hx, },
    { rw pi.single_eq_of_ne hj,
      exact h j, }, },
end

def add_submonoid.of_pi {ι : Type*} {B : ι → Type*} [decidable_eq ι]
  [Π i, add_zero_class (B i)] :
  add_submonoid (Π i, B i) → Π i, add_submonoid (B i) :=
λ h i,
{ carrier := λ x, x ∈ set.of_pi h.carrier i,
  zero_mem' := by {  simp_rw [set.of_pi, add_submonoid.mem_carrier, set.mem_def, pi.single_zero],
    exact h.zero_mem', },
  add_mem' := λ x y hx hy, by { have := h.add_mem' hx hy,
    simp only [add_submonoid.mem_carrier, ← pi.single_add] at this ⊢,
    exact this, }, }

lemma add_submonoid.pi_of_pi {ι : Type*} {B : ι → Type*} [decidable_eq ι]
  [Π i, add_zero_class (B i)] (h : Π i, add_submonoid (B i)) :
  (add_submonoid.pi set.univ h).of_pi = h :=
begin
  ext i x,
  simp_rw [add_submonoid.of_pi, add_submonoid.pi, add_submonoid.mem_mk],
  rw [set.pi_of_pi],
  refl,
  exact (λ i, (h i).zero_mem),
end

lemma set.of_pi_mem' {ι : Type*} {B : ι → Type*} [decidable_eq ι]
  [Π i, add_zero_class (B i)] {s : Π i, set (B i)}
  {S : set (Π i, B i)} (hs : set.univ.pi s ⊆ S)
  (h : ∀ i, s i 0) (i : ι) :
  s i ⊆ (S.of_pi i) :=
begin
  intros x hx,
  simp_rw [set.of_pi, set.mem_def] at ⊢ hx,
  apply hs,
  intros j hj,
  by_cases hj : j = i,
  { rw hj,
    rw [pi.single_eq_same],
    exact hx, },
  { rw pi.single_eq_of_ne hj,
    exact h j, },
end

lemma add_submonoid.closure_pi {ι : Type*} {B : ι → Type*}
  [decidable_eq ι] [Π i, add_zero_class (B i)]
  {s : Π i, set (B i)} {x : Π i, B i} :
  x ∈ add_submonoid.closure (set.univ.pi (λ i, s i))
    →
  ∀ i, x i ∈ add_submonoid.closure (s i)
   :=
begin
  simp_rw [add_submonoid.pi, add_submonoid.mem_closure],
  intro h,
  -- split,
  { rintros i S hS,
    specialize h (add_submonoid.pi set.univ (λ i, add_submonoid.closure (s i))),
    simp_rw [set.subset_def, set.mem_univ_pi, add_submonoid.pi, set_like.mem_coe,
      add_submonoid.mem_mk, set.mem_univ_pi, add_submonoid.mem_carrier,
      add_submonoid.mem_closure] at h,
    exact h (λ y hy j K hK, hK (hy j)) i S hS, },
end

lemma pi.star_ordered_ring.nonneg_def {ι : Type*}
  {α : ι → Type*} [Π i, non_unital_semiring (α i)] [Π i, partial_order (α i)]
  [Π i, star_ordered_ring (α i)] (h : ∀ (i : ι) (x : α i), 0 ≤ x ↔ ∃ y, star y * y = x)
  (x : Π i, α i) :
  0 ≤ x ↔ ∃ y, star y * y = x :=
begin
  simp_rw [pi.le_def, pi.zero_apply, function.funext_iff, pi.mul_apply,
    pi.star_apply, h],
  refine ⟨λ hx, ⟨(λ i, (hx i).some), λ i, (hx i).some_spec⟩,
    λ ⟨y, hy⟩ i, ⟨y i, (hy i)⟩⟩,
end
lemma pi.star_ordered_ring.le_def {ι : Type*}
  {α : ι → Type*} [Π i, ring (α i)] [Π i, partial_order (α i)]
  [Π i, star_ordered_ring (α i)] (h : ∀ (i : ι) (x : α i), 0 ≤ x ↔ ∃ y, star y * y = x)
  (x y : Π i, α i) :
  x ≤ y ↔ ∃ z, star z * z = y - x :=
begin
  calc x ≤ y ↔ 0 ≤ y - x : by simp only [sub_nonneg]
  ... ↔ ∃ z, star z * z = y - x : _,
  rw ← pi.star_ordered_ring.nonneg_def,
  exact h,
end

def pi.star_ordered_ring {ι : Type*} {B : ι → Type*}
  [Π i, ring (B i)] [Π i, partial_order (B i)] [Π i, star_ordered_ring (B i)]
  (h : ∀ (i : ι) (x : B i), 0 ≤ x ↔ ∃ y, star y * y = x) :
  star_ordered_ring (Π i, B i) :=
begin
  apply star_ordered_ring.of_le_iff,
  { intros a b hab c i,
    simp_rw [pi.add_apply],
    exact add_le_add_left (hab i) (c i), },
  { intros a b,
    rw [pi.star_ordered_ring.le_def h],
    simp_rw [eq_sub_iff_add_eq', eq_comm], },
end
