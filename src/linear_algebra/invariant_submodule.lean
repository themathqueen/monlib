/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.projection
import linear_algebra.tensor_product
import topology.algebra.star_subalgebra
import data.complex.basic

/-!
# Invariant submodules

In this file, we define and prove some basic results on invariant submodules.
-/

namespace submodule

variables {E R : Type*} [ring R] [add_comm_group E] [module R E]

/-- `U` is `T` invariant (ver 1): `U ≤ U.comap` -/
def invariant_under (U : submodule R E) (T : E →ₗ[R] E) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
@[simp] lemma invariant_under_iff_map (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ U.map T ≤ U := submodule.map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `set.maps_to T U U` -/
lemma invariant_under_iff_maps_to (U : submodule R E) (T : E →ₗ[R] E) :
  set.maps_to T U U ↔ U.invariant_under T := iff.rfl

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
lemma invariant_under_iff (U : submodule R E) (T : E →ₗ[R] E) :
  U.invariant_under T ↔ T '' U ⊆ U := by rw [← set.maps_to', U.invariant_under_iff_maps_to]

variables (U V : submodule R E) (hUV : is_compl U V) (T : E →ₗ[R] E)

local notation `pᵤ` := submodule.linear_proj_of_is_compl U V hUV
local notation `pᵥ` := submodule.linear_proj_of_is_compl V U hUV.symm

/-- projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p` -/
lemma linear_proj_of_is_compl_eq_self_iff {p q : submodule R E}
  (hpq : is_compl p q) (x : E) :
  (p.linear_proj_of_is_compl q hpq x : E) = x ↔ x ∈ p :=
begin
  split; intro H,
  { rw ← H, exact submodule.coe_mem _ },
  { exact congr_arg _ (submodule.linear_proj_of_is_compl_apply_left hpq ⟨x, H⟩) }
end

lemma invariant_under.linear_proj_comp_self_eq (h : U.invariant_under T) (x : U) :
  (pᵤ (T x) : E) = T x :=
(linear_proj_of_is_compl_eq_self_iff _ _).mpr $ h (coe_mem _)

lemma invariant_under_of_linear_proj_comp_self_eq (h : ∀ x : U, (pᵤ (T x) : E) = T x) :
  U.invariant_under T :=
λ u hu, by rw [mem_comap, ← linear_proj_of_is_compl_eq_self_iff hUV _,
      ← (linear_proj_of_is_compl_eq_self_iff hUV u).mpr hu, h]

/-- `U` is invariant under `T` if and only if `pᵤ ∘ₗ T = T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariant_under_iff_linear_proj_comp_self_eq :
  U.invariant_under T ↔ (∀ x : U, (pᵤ (T x) : E) = T x) :=
⟨invariant_under.linear_proj_comp_self_eq U V hUV T,
  invariant_under_of_linear_proj_comp_self_eq U V hUV T⟩

lemma linear_proj_of_is_compl_eq_self_sub_linear_proj {p q : submodule R E}
  (hpq : is_compl p q) (x : E) :
  (q.linear_proj_of_is_compl p hpq.symm x : E) = x - (p.linear_proj_of_is_compl q hpq x : E) :=
by rw [eq_sub_iff_add_eq, add_comm, submodule.linear_proj_add_linear_proj_of_is_compl_eq_self]

 /-- `V` is invariant under `T` if and only if `pᵤ ∘ₗ (T ∘ₗ pᵤ) = pᵤ ∘ₗ T`,
 where `pᵤ` denotes the linear projection to `U` along `V` -/
 lemma invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq :
   V.invariant_under T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x)) :=
 by simp_rw [invariant_under_iff_linear_proj_comp_self_eq _ _ hUV.symm,
             (linear_map.range_eq_top.1 (linear_proj_of_is_compl_range hUV.symm)).forall,
             linear_proj_of_is_compl_eq_self_sub_linear_proj, map_sub,
             sub_eq_self, submodule.coe_sub, sub_eq_zero, eq_comm]

 /-- both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
 where `pᵤ` denotes the linear projection to `U` along `V` -/
 lemma is_compl_invariant_under_iff_linear_proj_and_self_commute :
   (U.invariant_under T ∧ V.invariant_under T) ↔ commute (U.subtype ∘ₗ pᵤ) T :=
 begin
   simp_rw [commute, semiconj_by, linear_map.ext_iff, linear_map.mul_apply,
            linear_map.comp_apply, U.subtype_apply],
   split,
   { rintros ⟨h1, h2⟩ x,
     rw [← (U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq V _ _).mp h2 x],
     exact (linear_proj_of_is_compl_eq_self_iff hUV _).mpr (h1 (coe_mem (pᵤ x))) },
   { intros h,
     simp_rw [U.invariant_under_iff_linear_proj_comp_self_eq _ hUV,
              (linear_map.range_eq_top.1 (linear_proj_of_is_compl_range hUV)).forall,
              U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
              linear_proj_of_is_compl_idempotent hUV, ← forall_and_distrib, and_self,
              eq_self_iff_true, forall_const], }
 end

 /-- `U` is invariant under `T.symm` if and only if `U ⊆ T(U)` -/
 lemma invariant_under_symm_iff_le_map (T : E ≃ₗ[R] E) :
   U.invariant_under T.symm ↔ U ≤ U.map T :=
 (U.invariant_under_iff_map T.symm).trans (T.to_equiv.symm.subset_image' _ _).symm

lemma commutes_with_linear_proj_iff_linear_proj_eq [invertible T] :
  commute (U.subtype.comp pᵤ) T ↔
    (⅟ T).comp ((U.subtype.comp pᵤ).comp T) = U.subtype.comp pᵤ :=
begin
  rw [commute, semiconj_by],
  simp_rw [linear_map.mul_eq_comp],
  split,
  { intro h,
    simp_rw [h, ← linear_map.mul_eq_comp, ← mul_assoc, inv_of_mul_self, one_mul], },
  { intros h,
    rw ← h, simp_rw [← linear_map.mul_eq_comp, ← mul_assoc, mul_inv_of_self],
    rw [mul_assoc (⅟ T) _ _],
    simp_rw [linear_map.mul_eq_comp, h], refl, }
end

lemma invariant_under_inv_iff_U_subset_image [invertible T] :
  U.invariant_under (⅟ T) ↔ ↑U ⊆ T '' U :=
begin
  split,
 { intros h x hx,
   simp only [set.mem_image, set_like.mem_coe],
   use (⅟ T) x,
   rw [← linear_map.comp_apply, ← linear_map.mul_eq_comp,
       mul_inv_of_self, linear_map.one_apply, eq_self_iff_true, and_true],
   exact h hx, },
 { intros h x hx,
   rw submodule.mem_comap,
   simp only [set.subset_def, set.mem_image] at h,
   cases h x hx with y hy,
   rw [← hy.2, ← linear_map.comp_apply, ← linear_map.mul_eq_comp,
       inv_of_mul_self],
   exact hy.1 }
end

theorem inv_linear_proj_comp_map_eq_linear_proj_iff_images_eq [invertible T] :
  (⅟ T).comp ((U.subtype.comp pᵤ).comp T) = U.subtype.comp pᵤ ↔ T '' U = U ∧ T '' V = V :=
begin
  simp_rw [← submodule.commutes_with_linear_proj_iff_linear_proj_eq,
    ← is_compl_invariant_under_iff_linear_proj_and_self_commute,
    set.subset.antisymm_iff],
  have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ (q ∧ s)) := λ _ _ _ _, by
    { simp only [ and.assoc, eq_iff_iff, and.congr_right_iff],
      simp only [← and.assoc, and.congr_left_iff],
      simp only [and.comm], simp only [iff_self, implies_true_iff], },
  rw Hu,
  clear Hu,
  simp_rw [← submodule.invariant_under_iff _ _, iff_self_and,
    ← submodule.invariant_under_inv_iff_U_subset_image,
    is_compl_invariant_under_iff_linear_proj_and_self_commute U V hUV],
  rw [submodule.commutes_with_linear_proj_iff_linear_proj_eq, commute, semiconj_by],
  simp_rw [← linear_map.mul_eq_comp],
  intros h,
  rw ← h,
  simp_rw [mul_assoc _ _ (⅟ T), mul_inv_of_self, h],
  refl,
end

end submodule

lemma star_algebra.centralizer_prod {M : Type*} [add_comm_group M] [module ℂ M]
  [star_ring (M →ₗ[ℂ] M)] [star_module ℂ (M→ₗ[ℂ] M)] (A B : star_subalgebra ℂ (M →ₗ[ℂ] M)) :
  (A.carrier ×ˢ B.carrier).centralizer = A.carrier.centralizer ×ˢ B.carrier.centralizer :=
begin
  ext,
  simp_rw [set.mem_prod, set.mem_centralizer_iff, ← forall_and_distrib,
    set.mem_prod, and_imp, prod.forall, prod.mul_def, prod.eq_iff_fst_eq_snd_eq,
    star_subalgebra.mem_carrier],
  exact ⟨λ h y, ⟨λ hy, (h y 0 hy B.zero_mem').1, λ hy, (h 0 y A.zero_mem' hy).2⟩,
         λ h y z hy hz, ⟨(h y).1 hy, (h z).2 hz⟩⟩,
end
