/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.invariant_submodule
import linear_algebra.my_ips.basic
import linear_algebra.my_ips.ips
import analysis.von_neumann_algebra.basic
import linear_algebra.my_ips.minimal_proj
import linear_algebra.my_ips.rank_one

/-!

# A bit on von Neumann algebras

This file contains two simple results about von Neumann algebras.

-/

namespace von_neumann_algebra

variables {H : Type*} [normed_add_comm_group H] [inner_product_space ℂ H] [complete_space H]

/-- a continuous linear map `e` is in the von Neumann algebra `M`
if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem has_idempotent_iff_ker_and_range_are_invariant_under_commutant
  (M : von_neumann_algebra H) (e : H →L[ℂ] H) (h : is_idempotent_elem e) :
  e ∈ M ↔
    ∀ y : H →L[ℂ] H, y ∈ M.commutant → (e.ker).invariant_under y ∧ (e.range).invariant_under y :=
begin
  simp_rw [submodule.invariant_under_iff, set.subset_def,
          continuous_linear_map.to_linear_map_eq_coe,
          continuous_linear_map.coe_coe, set.mem_image, set_like.mem_coe,
          linear_map.mem_ker, linear_map.mem_range,
          continuous_linear_map.coe_coe, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂],
  split,
  { intros he y hy,
    have : e.comp y = y.comp e,
    { rw [← von_neumann_algebra.commutant_commutant M,
          von_neumann_algebra.mem_commutant_iff] at he,
      exact (he y hy).symm },
    simp_rw [← continuous_linear_map.comp_apply, this],
    exact ⟨ λ x hx, by rw [continuous_linear_map.comp_apply, hx, map_zero],
            λ u ⟨v, hv⟩, by simp_rw [← hv, ← continuous_linear_map.comp_apply, ← this,
                                    continuous_linear_map.comp_apply,
                                    exists_apply_eq_apply], ⟩ },
  { intros H,
    rw [← von_neumann_algebra.commutant_commutant M],
    intros m hm, ext x,
    have h' : is_idempotent_elem e.to_linear_map,
    { rw is_idempotent_elem at ⊢ h, ext y,
      rw [linear_map.mul_apply, continuous_linear_map.to_linear_map_eq_coe,
          continuous_linear_map.coe_coe, ← continuous_linear_map.mul_apply, h] },
    obtain ⟨v, w, hvw, hunique⟩ :=
      submodule.exists_unique_add_of_is_compl
      (linear_map.is_idempotent.is_compl_range_ker ↑e h') x,
    obtain ⟨y, hy⟩ := set_like.coe_mem w,
    have hg := linear_map.mem_ker.mp (set_like.coe_mem v),
    simp_rw [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe] at hy hg,
    rw [set_like.mem_coe] at hm,
    simp_rw [← hvw, continuous_linear_map.mul_apply, map_add, hg, map_zero, zero_add],
    obtain ⟨p,hp⟩ := (H m hm).2 (w) (set_like.coe_mem w),
    rw [(H m hm).1 v hg, zero_add, ← hp, ← continuous_linear_map.mul_apply e e,
        is_idempotent_elem.eq h, hp, ← hy, ← continuous_linear_map.mul_apply e e,
        is_idempotent_elem.eq h], }
end

/-- By definition, the bounded linear operators on a Hilbert space `H` form a von Neumann algebra.

  !!(But the note on the definition says that we can't do this because it's a bundled structure?)!! idk? -/
def of_Hilbert_space :
  von_neumann_algebra H :=
{ carrier := set.univ,
  mul_mem' := λ x y hx hy, set.mem_univ _,
  add_mem' := λ x y hx hy, set.mem_univ _,
  star_mem' := λ x hx, set.mem_univ _,
  algebra_map_mem' := λ x, set.mem_univ _,
  centralizer_centralizer' := continuous_linear_map.centralizer_centralizer, }

end von_neumann_algebra
