/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.projection

/-!
 # is_proj'

This file contains the definition of `linear_map.is_proj'` and lemmas relating to it, which is essentially `linear_map.is_proj` but as a linear map from `E` to `↥U`.

-/

section

variables {R E : Type*} [ring R] [add_comm_group E] [module R E] {U : submodule R E}

/-- `linear_map.is_proj` but as a linear map from `E` to `↥U` -/
def is_proj' {p : E →ₗ[R] E} (hp : linear_map.is_proj U p) :
  E →ₗ[R] ↥U :=
{ to_fun := λ x, ⟨p x, hp.1 x⟩,
  map_add' := λ x y, by { simp_rw [map_add, add_mem_class.mk_add_mk], },
  map_smul' := λ r x, by { simp_rw [linear_map.map_smul, ring_hom.id_apply, set_like.mk_smul_mk], } }

lemma is_proj'_apply {p : E →ₗ[R] E} (hp : linear_map.is_proj U p) (x : E) :
  ↑(is_proj' hp x) = p x :=
rfl

lemma is_proj'_eq
  {p : E →ₗ[R] E} (hp : linear_map.is_proj U p) :
  ∀ x : ↥U, is_proj' hp (x : E) = x :=
begin
  intros x,
  ext,
  simp_rw [is_proj'_apply, linear_map.is_proj.map_id hp _ (set_like.coe_mem x)],
end

end

variables {E 𝕜 : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]

lemma orthogonal_projection_eq_linear_proj' {K : submodule 𝕜 E} [complete_space K] :
  (orthogonal_projection K : E →ₗ[𝕜] K) =
  submodule.linear_proj_of_is_compl K _ submodule.is_compl_orthogonal_of_complete_space :=
begin
  have : is_compl K Kᗮ := submodule.is_compl_orthogonal_of_complete_space,
  ext x : 1,
  nth_rewrite 0 [← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self this x],
  rw [continuous_linear_map.coe_coe, map_add, orthogonal_projection_mem_subspace_eq_self,
      orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (submodule.coe_mem _),
      add_zero],
end

lemma orthogonal_projection_eq_linear_proj'' {K : submodule 𝕜 E} [complete_space K] (x : E) :
  orthogonal_projection K x =
  submodule.linear_proj_of_is_compl K _ submodule.is_compl_orthogonal_of_complete_space x :=
by rw [← orthogonal_projection_eq_linear_proj]; refl

noncomputable def orthogonal_projection' (U : submodule 𝕜 E) [complete_space U] :
  E →L[𝕜] E :=
U.subtypeL.comp (orthogonal_projection U)

lemma orthogonal_projection'_apply [inner_product_space 𝕜 E] (U : submodule 𝕜 E) [complete_space U]
  (x : E) :
  orthogonal_projection' U x = (orthogonal_projection U x) :=
rfl

local notation `P` := orthogonal_projection
local notation `↥P` := orthogonal_projection'

@[simp] lemma continuous_linear_map.range_to_linear_map {p : E →L[𝕜] E} :
  p.range = linear_map.range p :=
rfl

open continuous_linear_map

@[simp] lemma orthogonal_projection.range (U : submodule 𝕜 E) [complete_space U] :
  linear_map.range (↥P U) = U :=
by simp_rw [orthogonal_projection', ← range_to_linear_map, to_linear_map_eq_coe,
     coe_comp, orthogonal_projection_eq_linear_proj', submodule.coe_subtypeL,
     linear_map.range_comp, submodule.linear_proj_of_is_compl_range, submodule.map_subtype_top]

@[simp] lemma orthogonal_projection'_eq (U : submodule 𝕜 E) [complete_space U] :
  ↥P U = U.subtypeL.comp (P U) :=
rfl

lemma orthogonal_projection'_eq_linear_proj {K : submodule 𝕜 E} [complete_space K] :
  (K.subtypeL.comp (orthogonal_projection K) : E →ₗ[𝕜] E) = K.subtype.comp
  (submodule.linear_proj_of_is_compl K _ submodule.is_compl_orthogonal_of_complete_space) :=
begin
  ext x,
  simp_rw [continuous_linear_map.coe_coe, linear_map.comp_apply, continuous_linear_map.comp_apply,
    submodule.subtypeL_apply, submodule.subtype_apply, orthogonal_projection_eq_linear_proj''],
end

lemma orthogonal_projection'_eq_linear_proj' {K : submodule 𝕜 E} [complete_space K] (x : E) :
  (orthogonal_projection' K : E →ₗ[𝕜] E) x = K.subtype.comp
    (submodule.linear_proj_of_is_compl K _ submodule.is_compl_orthogonal_of_complete_space) x :=
by rw [← orthogonal_projection'_eq_linear_proj, orthogonal_projection']
