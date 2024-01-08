/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.symm

/-!

# Some obvious basic properties on inner product space

This files provides some useful and obvious results for linear maps and continuous linear maps.

-/

lemma inner_self_re {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x : E) :
  (is_R_or_C.re (inner x x : 𝕜) : 𝕜) = inner x x :=
begin
  simp only [inner_self_re_to_K],
end

lemma forall_inner_eq_zero_iff {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x : E) :
  (∀ y, (inner x y : 𝕜) = 0) ↔ x = 0 :=
begin
  refine ⟨λ h, _, λ h y, by rw [h, inner_zero_left]⟩,
  specialize h x,
  rw [inner_self_eq_zero] at h,
  exact h,
end


open is_R_or_C continuous_linear_map

variables {E : Type*} [normed_add_comm_group E]

/-- linear maps $p,q$ are equal if and only if
  $\langle p x, x \rangle = \langle q x, x \rangle$ for any $x$. -/
lemma linear_map.ext_iff_inner_map [inner_product_space ℂ E] (p q : E →ₗ[ℂ] E) :
  p = q ↔ ∀ x : E, ⟪p x, x⟫_ℂ = ⟪q x, x⟫_ℂ :=
begin
  split,
  { intros h,
    simp_rw [h, eq_self_iff_true, forall_const], },
  { intros h,
    rw [← sub_eq_zero, ← inner_map_self_eq_zero],
    simp_rw [linear_map.sub_apply, inner_sub_left, h, sub_self, forall_const], },
end

/-- copy of `linear_map.ext_iff_inner_map` but for continuous linear maps -/
lemma continuous_linear_map.ext_iff_inner_map [inner_product_space ℂ E] (p q : E →L[ℂ] E) :
  p = q ↔ ∀ x : E, ⟪p x, x⟫_ℂ = ⟪q x, x⟫_ℂ :=
begin
  simp_rw [← continuous_linear_map.coe_coe, ← linear_map.ext_iff_inner_map,
    coe_inj],
end

/-- Self-adjoint linear operators $p,q$ are equal if and only if
  $\langle p x, x \rangle_\mathbb{k} = \langle q x, x \rangle_\mathbb{k}$. -/
lemma continuous_linear_map.is_self_adjoint.ext_iff_inner_map {E 𝕜 : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E] {p q : E →L[𝕜] E}
  (hp : is_self_adjoint p) (hq : is_self_adjoint q) :
  p = q ↔ ∀ x : E, @inner 𝕜 _ _ (p x) x = @inner 𝕜 _ _ (q x) x :=
begin
  rw [← sub_eq_zero, ← is_self_adjoint.inner_map_self_eq_zero (is_self_adjoint.sub hp hq)],
  simp_rw [sub_apply, inner_sub_left, sub_eq_zero],
end


section is_R_or_C


variables {𝕜 : Type*} [is_R_or_C 𝕜]

/-- in a complex inner product space, we have
  that an operator $a$ is self-adjoint if and only if
  $\langle a x, x \rangle_\mathbb{C}$ is real for all $x \in E$ -/
lemma is_self_adjoint_iff_complex_inner_re_eq
  [inner_product_space ℂ E] [complete_space E] {a : E →L[ℂ] E} :
  is_self_adjoint a ↔ ∀ x : E, (re ⟪a x, x⟫_ℂ : ℂ) = ⟪a x, x⟫_ℂ :=
begin
  simp_rw [re_to_complex, ← complex.conj_eq_iff_re, inner_conj_symm,
    is_self_adjoint_iff', continuous_linear_map.ext_iff_inner_map a.adjoint a,
    adjoint_inner_left],
end

local notation `⟪` x `,` y `⟫` := @inner 𝕜 _ _ x y

/-- the adjoint of a self-adjoint operator is self-adjoint -/
lemma is_self_adjoint.adjoint [inner_product_space 𝕜 E] [complete_space E] {a : E →L[𝕜] E}
  (ha : is_self_adjoint a) :
  is_self_adjoint a.adjoint :=
congr_arg star ha

/-- for a self-adjoint operator $a$, we have $\langle a x, x \rangle_\mathbb{k}$ is real -/
lemma is_self_adjoint.inner_re_eq {E : Type*} [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [complete_space E] {a : E →L[𝕜] E}
  (ha : is_self_adjoint a) (x : E) :
  (re ⟪a x, x⟫ : 𝕜) = ⟪a x, x⟫ :=
begin
  rcases @I_mul_I_ax 𝕜 _ with (h | h),
  { rw ← re_add_im ⟪a x, x⟫,
    simp_rw [h, mul_zero, add_zero],
    norm_cast, },
  { simp_rw [← conj_eq_iff_re, inner_conj_symm],
    have ha' := ha,
    simp_rw [is_self_adjoint_iff',
      continuous_linear_map.is_self_adjoint.ext_iff_inner_map ha.adjoint ha,
      adjoint_inner_left] at ha',
    exact ha' x, },
end

end is_R_or_C

/-- copy of `inner_map_self_eq_zero` for bounded linear maps -/
lemma continuous_linear_map.inner_map_self_eq_zero [inner_product_space ℂ E]
  [complete_space E] {p : E →L[ℂ] E} :
  (∀ x : E, ⟪p x, x⟫_ℂ = 0) ↔ p = 0 :=
begin
  simp_rw [continuous_linear_map.ext_iff, ← continuous_linear_map.coe_coe,
    ← continuous_linear_map.to_linear_map_eq_coe, ← linear_map.ext_iff],
  exact inner_map_self_eq_zero p.to_linear_map,
end

lemma continuous_linear_map.adjoint_smul {K E : Type*} [is_R_or_C K]
  [normed_add_comm_group E] [inner_product_space K E] [complete_space E] (φ : E →L[K] E) (a : K) :
  (a • φ).adjoint = star_ring_end K a • φ.adjoint :=
begin
  simp_rw [← continuous_linear_map.star_eq_adjoint, star_smul, star_ring_end_apply],
end
lemma linear_map.adjoint_smul {K E : Type*} [is_R_or_C K]
  [normed_add_comm_group E] [inner_product_space K E] [finite_dimensional K E]
  (φ : E →ₗ[K] E) (a : K) :
  (a • φ).adjoint = star_ring_end K a • φ.adjoint :=
begin
  have := @continuous_linear_map.adjoint_smul K E _ _ _ (finite_dimensional.complete K E)
    φ.to_continuous_linear_map a,
  simp_rw [← linear_map.adjoint_to_continuous_linear_map] at this,
  rw [linear_map.adjoint_eq_to_clm_adjoint, smul_hom_class.map_smul, this],
  refl,
end
