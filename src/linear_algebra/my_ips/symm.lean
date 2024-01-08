/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.symmetric
import analysis.inner_product_space.adjoint

/-!

# some obvious lemmas on self-adjoint operators

This file provides the polarization identity for self adjoint continuous linear maps
  over `is_R_or_C`.

-/

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
local notation `⟪`x`,`y`⟫` := @inner 𝕜 _ _ x y

namespace continuous_linear_map

/-- Given a self-adjoint continuous linear operator $T$ on $E$, we get
  $\langle T x, x \rangle = 0$ for any $x\in E$ if and only if $T=0$. -/
lemma is_self_adjoint.inner_map_self_eq_zero [complete_space E]
  {T : E →L[𝕜] E} (hT : is_self_adjoint T) :
  (∀ x, ⟪T x, x⟫ = 0) ↔ T = 0 :=
begin
  simp_rw [ext_iff, ← continuous_linear_map.coe_coe, ← linear_map.ext_iff, coe_zero],
  simp_rw [is_self_adjoint_iff_is_symmetric] at hT,
  exact hT.inner_map_self_eq_zero,
end

open is_R_or_C

/-- The polarization identity for self-adjoint operators. -/
lemma is_self_adjoint.inner_map_polarization [complete_space E]
  {T : E →L[𝕜] E} (hT : is_self_adjoint T) (x y : E) :
  ⟪T x, y⟫ = (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ -
    I * ⟪T (x + (I : 𝕜) • y), x + (I : 𝕜) • y⟫ +
    I * ⟪T (x - (I : 𝕜) • y), x - (I : 𝕜) • y⟫) / 4 :=
by rw [← continuous_linear_map.coe_coe,
       linear_map.is_symmetric.inner_map_polarization (is_self_adjoint.is_symmetric hT)]

end continuous_linear_map
