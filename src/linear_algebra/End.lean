/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.eigenspace.basic

/-!
 # Some obvious lemmas on module.End

This file contains some obvious lemmas on `module.End`.
-/

open_locale big_operators

lemma linear_map.comp_one {R E F : Type*} [semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R F] [module R E] (f : E →ₗ[R] F) :
  f ∘ₗ (1 : E →ₗ[R] E) = f :=
by { rw [linear_map.one_eq_id, linear_map.comp_id], }

lemma linear_map.one_comp {R E F : Type*} [semiring R] [add_comm_monoid E]
  [add_comm_monoid F] [module R F] [module R E] (f : E →ₗ[R] F) :
  (1 : F →ₗ[R] F) ∘ₗ f = f :=
by { rw [linear_map.one_eq_id, linear_map.id_comp], }

lemma linear_map.comp_sum {R M M₂ M₃ : Type*} [semiring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [module R M] [module R M₂] [module R M₃]
  (g : M₃ →ₗ[R] M₂) {α : Type*} (s : finset α) (f : α → (M →ₗ[R] M₃)) :
  g ∘ₗ (∑ (a : α) in s, f a) = ∑ (a : α) in s, (g ∘ₗ (f a)) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.sum_apply, linear_map.comp_apply,
    linear_map.sum_apply, map_sum, eq_self_iff_true, forall_true_iff],
end

lemma linear_map.sum_comp {R M M₂ M₃ : Type*} [semiring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [module R M] [module R M₂] [module R M₃]
  (f : M →ₗ[R] M₃) {α : Type*} (s : finset α) (g : α → (M₃ →ₗ[R] M₂)) :
  (∑ (a : α) in s, g a) ∘ₗ f = ∑ (a : α) in s, ((g a) ∘ₗ f) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.sum_apply, linear_map.comp_apply,
    linear_map.sum_apply, eq_self_iff_true, forall_true_iff],
end

lemma module.End.has_eigenvector_iff_has_eigenvalue
  {R M : Type*} [comm_ring R] [add_comm_group M] [module R M] {T : module.End R M} {α : R} :
  (∃ v : M, T v = α • v ∧ v ≠ 0) ↔ module.End.has_eigenvalue T α :=
begin
  split,
  { rintros ⟨v, hv⟩,
    apply module.End.has_eigenvalue_of_has_eigenvector,
    rw [module.End.has_eigenvector, module.End.mem_eigenspace_iff],
    exact hv, },
  { intros h,
    rw module.End.has_eigenvalue at h,
    simp_rw submodule.ne_bot_iff at h,
    rcases h with ⟨x, Hx, hx⟩,
    use x,
    rw ← module.End.mem_eigenspace_iff,
    exact ⟨Hx, hx⟩, },
end
