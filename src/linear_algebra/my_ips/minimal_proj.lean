/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.pos
import linear_algebra.my_ips.ips
import linear_algebra.my_ips.symm
import rep_theory.aut_mat
import linear_algebra.kronecker_to_tensor
import linear_algebra.matrix.hermitian
import linear_algebra.my_ips.rank_one
import linear_algebra.my_ips.basic
import linear_algebra.is_proj'
import analysis.inner_product_space.orthogonal

/-!

# Minimal projections

In this file we show some necessary results for positive operators on a Hilbert space.

## main results

**Theorem.** If $p,q$ are (orthogonal) projections on $E$,
  then the following are equivalent:
   - (i) $pq = p = qp$
   - (ii) $p(E) \subseteq q(E)$
   - (iii) $q - p$ is an (orthogonal) projection
   - (iv) $q - p$ is positive

for part (iii), it suffices to show that the element is an idempotent since
  $q - p$ is self-adjoint

it turns out that $qp = p$ (from (i)) if and only if (ii) and
  (i) if and only if (iii) for idempotent operators on a module over a ring
  (see `is_idempotent_elem.comp_idempotent_iff` and
   `linear_map.commutes_iff_is_idempotent_elem`)

obviously when $p,q$ are self-adjoint operators, then $pq = p$ iff $qp=p$
  (see `self_adjoint_commutes_iff`)

so then, obviously, (ii) if and only if (iii) for idempotent self-adjoint operators as well
  (see `continuous_linear_map.image_subset_iff_sub_of_is_idempotent`)

we finally have (i) if and only if (iv) for idempotent self-adjoint operators on a
  finite-dimensional complex-Hilbert space:
  (see `orthogonal_projection_is_positive_iff_commutes`)

## main definition

* an operator is non-negative means that it is positive:
  $0 \leq p$ if and only if $p$ is positive
  (see `is_positive.is_nonneg`)

-/

section

variables {R E : Type*} [ring R] [add_comm_group E] [module R E]
open submodule linear_map

/-- given an idempotent linear operator $p$, we have
  $x \in \textnormal{range}(p)$ if and only if $p(x) = x$ (for all $x \in E$) -/
lemma is_idempotent_elem.mem_range_iff {p : E →ₗ[R] E}
  (hp : is_idempotent_elem p) {x : E} :
  x ∈ p.range ↔ p x = x :=
begin
  simp_rw [mem_range],
  split,
  { rintros ⟨y, hy⟩,
    nth_rewrite 0 ← hy,
    rw [← mul_apply, hp.eq, hy], },
  { intros h,
    use x,
    exact h, },
end

variables {U V : submodule R E} {p q : E →ₗ[R] E}
  (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)

include hq
/-- given idempotent linear operators $p,q$,
  we have $qp = p$ iff $p(E) \subseteq q(E)$ -/
theorem is_idempotent_elem.comp_idempotent_iff :
  q.comp p = p ↔ map p ⊤ ≤ map q ⊤ :=
by simp_rw [ext_iff, comp_apply, ← is_idempotent_elem.mem_range_iff hq,
            submodule.map_top, set_like.le_def, mem_range,
            forall_exists_index, forall_apply_eq_imp_iff']

include hp

/-- if $p,q$ are idempotent operators and $pq = p = qp$,
  then $q - p$ is an idempotent operator -/
lemma linear_map.is_idempotent_elem_sub_of
  (h : p.comp q = p ∧ q.comp p = p) : is_idempotent_elem (q - p) :=
by simp_rw [is_idempotent_elem, mul_eq_comp, sub_comp, comp_sub, h.1, h.2,
            ← mul_eq_comp, hp.eq, hq.eq, sub_self, sub_zero]

/-- if $p,q$ are idempotent operators and $q - p$ is also an idempotent
  operator, then $pq = p = qp$ -/
lemma linear_map.commutes_of_is_idempotent_elem
  {E 𝕜 : Type*} [is_R_or_C 𝕜] [add_comm_group E] [module 𝕜 E]
  {p q : E →ₗ[𝕜] E} (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)
  (h : is_idempotent_elem (q - p)) : p.comp q = p ∧ q.comp p = p :=
begin
  simp_rw [is_idempotent_elem, mul_eq_comp, comp_sub, sub_comp,
            ← mul_eq_comp, hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj,
            add_sub] at h,
  have h' : (2 : 𝕜) • p = q.comp p + p.comp q,
  { simp_rw two_smul,
    nth_rewrite 1 ← h,
    simp_rw [mul_eq_comp, add_sub_cancel'_right, add_comm], },
  have H : ((2 : 𝕜) • p).comp q = q.comp (p.comp q) + p.comp q,
  { simp_rw [h', add_comp, comp_assoc, ← mul_eq_comp, hq.eq], },
  simp_rw [add_comm, two_smul, add_comp, add_right_inj] at H,
  have H' : q.comp ((2 : 𝕜) • p) = q.comp p + q.comp (p.comp q),
  { simp_rw [h', comp_add, ← comp_assoc, ← mul_eq_comp, hq.eq], },
  simp_rw [two_smul, comp_add, add_right_inj] at H',
  have H'' : q.comp p = p.comp q,
  { simp_rw [H'],
    exact H.symm, },
  rw [← H'', and_self, ← smul_right_inj (two_ne_zero), h', ← H'', two_smul],
  exact linear_map.no_zero_smul_divisors,
  exact invertible.ne_zero 2,
end

/-- given idempotent operators $p,q$,
  we have $pq = p = qp$ iff $q - p$ is an idempotent operator -/
theorem linear_map.commutes_iff_is_idempotent_elem
  {E 𝕜 : Type*} [is_R_or_C 𝕜] [add_comm_group E] [module 𝕜 E]
  {p q : E →ₗ[𝕜] E} (hp : is_idempotent_elem p) (hq : is_idempotent_elem q) :
  (p.comp q = p ∧ q.comp p = p) ↔ is_idempotent_elem (q - p) :=
⟨λ h, linear_map.is_idempotent_elem_sub_of hp hq h,
 λ h, linear_map.commutes_of_is_idempotent_elem hp hq h⟩

end

open continuous_linear_map
variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]

local notation `P` := orthogonal_projection

/-- given self-adjoint operators $p,q$,
  we have $pq=p$ iff $qp=p$ -/
theorem self_adjoint_proj_commutes [inner_product_space 𝕜 E] [complete_space E]
  {p q : E →L[𝕜] E} (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) :
  p.comp q = p ↔ q.comp p = p :=
begin
  have : function.injective (λ (a₁ : E →L[𝕜] E), star a₁),
  { intros x y h,
    simp_rw ← star_eq_adjoint at h,
    exact star_injective h, },
  split;
  intros h;
  { apply_fun adjoint,
    simp only [adjoint_comp, is_self_adjoint_iff'.mp hpa,
               is_self_adjoint_iff'.mp hqa, h],
    exact _inst_4, },
end

local notation `↥P` := orthogonal_projection'

lemma orthogonal_projection.idempotent [inner_product_space 𝕜 E]
  (U : submodule 𝕜 E) [complete_space U] :
  is_idempotent_elem (↥P U) :=
begin
  rw is_idempotent_elem,
  ext,
  simp_rw [mul_apply, orthogonal_projection'_eq, comp_apply, submodule.subtypeL_apply,
    orthogonal_projection_mem_subspace_eq_self],
end

def continuous_linear_map.is_orthogonal_projection [inner_product_space 𝕜 E]
  (T : E →L[𝕜] E) : Prop :=
is_idempotent_elem T ∧ T.ker = (T.range)ᗮ

/-- given any idempotent operator $T ∈ L(V)$, then `is_compl T.ker T.range`,
in other words, there exists unique $v ∈ \textnormal{ker}(T)$ and $w ∈ \textnormal{range}(T)$ such that $x = v + w$ -/
lemma linear_map.is_idempotent.is_compl_range_ker {V R : Type*} [ring R] [add_comm_group V]
  [module R V] (T : V →ₗ[R] V) (h : is_idempotent_elem T) :
  is_compl T.ker T.range :=
begin
 split,
   { rw disjoint_iff,
     ext,
     simp only [submodule.mem_bot, submodule.mem_inf, linear_map.mem_ker,
                linear_map.mem_range, continuous_linear_map.to_linear_map_eq_coe,
                continuous_linear_map.coe_coe],
     split,
       { intro h',
         cases h'.2 with y hy,
         rw [← hy, ← is_idempotent_elem.eq h, linear_map.mul_apply, hy],
         exact h'.1, },
       { intro h',
         rw [h', map_zero],
         simp only [eq_self_iff_true, true_and],
         use x,
         simp only [h', map_zero, eq_self_iff_true], }, },
    { suffices : ∀ x : V, ∃ v : T.ker, ∃ w : T.range, x = v + w,
        { rw [codisjoint_iff, ← submodule.add_eq_sup],
          ext,
          rcases this x with ⟨v,w,hvw⟩,
          simp only [submodule.mem_top, iff_true, hvw],
          apply submodule.add_mem_sup (set_like.coe_mem v) (set_like.coe_mem w), },
      intro x,
      use (x-(T x)), rw [linear_map.mem_ker, map_sub,
                         ← linear_map.mul_apply, is_idempotent_elem.eq h, sub_self],
      use (T x), rw [linear_map.mem_range]; simp only [exists_apply_eq_apply],
      simp only [submodule.coe_mk, sub_add_cancel], }
end

lemma is_compl.of_orthogonal_projection [inner_product_space 𝕜 E]
  {T : E →L[𝕜] E} (h : T.is_orthogonal_projection) :
  is_compl T.ker T.range :=
linear_map.is_idempotent.is_compl_range_ker _ ((is_idempotent_elem.to_linear_map _).mp h.1)

lemma orthogonal_projection.is_orthogonal_projection [inner_product_space ℂ E]
  {U : submodule ℂ E} [complete_space E] [complete_space U] :
  (↥P U).is_orthogonal_projection :=
⟨(orthogonal_projection.idempotent U : is_idempotent_elem (U.subtypeL.comp (P U) : E →L[ℂ] E)),
 (is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range (U.subtypeL.comp (P U) : E →L[ℂ] E)
 (orthogonal_projection.idempotent U : is_idempotent_elem (U.subtypeL.comp (P U) : E →L[ℂ] E))).mp
(orthogonal_projection_is_self_adjoint U)⟩

lemma is_idempotent_elem.clm_to_lm [inner_product_space 𝕜 E] {T : E →L[𝕜] E} :
  is_idempotent_elem T ↔ is_idempotent_elem (T : E →ₗ[𝕜] E) :=
begin
  simp_rw [is_idempotent_elem, linear_map.mul_eq_comp, ← coe_comp, coe_inj],
  refl,
end

/-- $P_V P_U = P_U$ if and only if $P_V - P_U$ is an orthogonal projection -/
lemma sub_of_is_orthogonal_projection [inner_product_space ℂ E] [complete_space E]
  {U V : submodule ℂ E} [complete_space U] [complete_space V] :
  (↥P V).comp (↥P U) = (↥P U)
  ↔ (↥P V - ↥P U).is_orthogonal_projection :=
begin
  let p := ↥P U,
  let q := ↥P V,
  have pp : p = U.subtypeL.comp (P U) := rfl,
  have qq : q = V.subtypeL.comp (P V) := rfl,
  have hp : is_idempotent_elem p := orthogonal_projection.idempotent U,
  have hq : is_idempotent_elem q := orthogonal_projection.idempotent V,
  have hpa := orthogonal_projection_is_self_adjoint U,
  have hqa := orthogonal_projection_is_self_adjoint V,
  have h2 := self_adjoint_proj_commutes hpa hqa,
  simp_rw [orthogonal_projection', ← pp, ← qq] at *,
  split,
  { intros h,
    have h_and : (p : E →ₗ[ℂ] E) ∘ₗ (q : E →ₗ[ℂ] E) = p
      ∧ (q : E →ₗ[ℂ] E) ∘ₗ (p : E →ₗ[ℂ] E) = p,
    { simp_rw [← coe_comp, coe_inj, h2, and_self, h], },
    rw [linear_map.commutes_iff_is_idempotent_elem (is_idempotent_elem.clm_to_lm.mp hp)
        (is_idempotent_elem.clm_to_lm.mp hq), ← coe_sub, ← is_idempotent_elem.clm_to_lm] at h_and,
    refine ⟨h_and, _⟩,
    rw ← is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ h_and,
    exact is_self_adjoint.sub hqa hpa, },
  { rintros ⟨h1, h3⟩,
    simp_rw [is_idempotent_elem.clm_to_lm, coe_sub,
      ← linear_map.commutes_iff_is_idempotent_elem (is_idempotent_elem.clm_to_lm.mp hp)
        (is_idempotent_elem.clm_to_lm.mp hq), ← coe_comp, coe_inj] at h1,
    exact h1.2, },
end

section

/-- instance for `≤` on linear maps -/
instance linear_map.is_symmetric.has_le {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] :
  has_le (E →ₗ[𝕜] E) :=
begin
  refine {le := _},
  intros u v,
  exact (v - u : E →ₗ[𝕜] E).is_positive,
end

local notation `sa`g := {x : g →ₗ[ℂ] g | x.is_symmetric}
local notation `SA`g := {x : g →L[ℂ] g | is_self_adjoint x}
local notation `L(` x `,` y `)` := x →L[y] x
local notation `l(` x `,` y `)` := x →ₗ[y] x

instance {E : Type*} [normed_add_comm_group E] [inner_product_space ℂ E] :
  partial_order sa E :=
begin
  fconstructor,
  { intros u v,
    exact (v - u : E →ₗ[ℂ] E).is_positive, },
  { intros a,
    simp_rw [sub_self],
    split,
    { intros u v,
      simp_rw [linear_map.zero_apply, inner_zero_left, inner_zero_right], },
    { intros x,
      simp_rw [linear_map.zero_apply, inner_zero_right, is_R_or_C.zero_re'], }, },
  { simp_rw [has_le.le],
    intros a b c hab hbc,
    rw [← add_zero ↑c, ← sub_self ↑b, ← add_sub_assoc, add_sub_right_comm, add_sub_assoc],
    exact linear_map.is_positive.add hbc hab, },
  { simp_rw [has_le.le],
    rintros a b hba hab,
    simp_rw [subtype.coe_inj.symm, linear_map.ext_iff_inner_map],
    intros x,
    have hba2 := hba.2 x,
    rw [← neg_le_neg_iff, ← map_neg, ← inner_neg_right, ← linear_map.neg_apply, neg_sub,
        neg_zero] at hba2,
    rw [← sub_eq_zero, ← inner_sub_left, ← linear_map.sub_apply, hab.1,
        ← ((linear_map.complex_is_positive _).mp hab _).1,
        le_antisymm hba2 (hab.2 x), complex.of_real_zero], },
end

/-- `p ≤ q` means `q - p` is positive -/
lemma linear_map.is_positive.has_le {E: Type*} [normed_add_comm_group E] [inner_product_space ℂ E]
  {p q : sa E} :
  p ≤ q ↔ (q - p : l(E,ℂ)).is_positive :=
by refl

noncomputable instance is_symmetric.has_zero {E : Type*} [normed_add_comm_group E]
  [inner_product_space ℂ E] :
  has_zero ↥{x : E →ₗ[ℂ] E | x.is_symmetric} :=
begin
  fconstructor,
  fconstructor,
  exact 0,
  simp_rw [set.mem_set_of_eq, linear_map.is_symmetric, linear_map.zero_apply,
    inner_zero_left, inner_zero_right, forall_const],
end


/-- saying `p` is positive is the same as saying `0 ≤ p` -/
lemma linear_map.is_positive.is_nonneg {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] {p : l(E, 𝕜)} :
  p.is_positive ↔ 0 ≤ p :=
begin
  nth_rewrite 0 ← sub_zero p,
  refl,
end

end

section

/-- instance for `≤` on bounded linear maps -/
instance {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [complete_space E] : has_le (E →L[𝕜] E) :=
begin
  refine {le := _},
  intros u v,
  exact is_positive (v - u),
end

/-- when `a,b` are self-adjoint operators, then
  if `a ≤ b` and `b ≤ a`, then `a = b` -/
lemma is_self_adjoint.has_le.le_antisymm {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [complete_space E] {a b : E →L[𝕜] E}
  (ha : is_self_adjoint a) (hb : is_self_adjoint b) (hab : a ≤ b) (hba : b ≤ a) :
  a = b :=
begin
  simp_rw [has_le.le] at *,
  rw [continuous_linear_map.is_self_adjoint.ext_iff_inner_map ha hb],
  intros x,
  have hba2 := hba.2 x,
  rw [← neg_le_neg_iff, re_apply_inner_self_apply, ← map_neg, ← inner_neg_left,
    ← neg_apply, neg_sub, neg_zero] at hba2,
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, ← sub_apply, ← is_self_adjoint.inner_re_eq hab.1 x,
    is_R_or_C.of_real_eq_zero, le_antisymm (hab.2 x) hba2],
  refl,
end

/-- we always have `a ≤ a` -/
@[refl, simp] lemma continuous_linear_map.has_le.le_refl {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E] {a : E →L[𝕜] E} :
  a ≤ a :=
by simp_rw [has_le.le, sub_self, is_positive_zero]

/-- when `a,b` are self-adjoint operators, then
  if `a ≤ b` and `b ≤ c`, then `a ≤ c` -/
@[simp] lemma is_self_adjoint.has_le.le_trans {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [complete_space E] {a b c : E →L[𝕜] E} (ha : is_self_adjoint a) (hb : is_self_adjoint b)
  (hc : is_self_adjoint c)
  (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  simp_rw [has_le.le] at *,
  rw [← add_zero c, ← sub_self b, ← add_sub_assoc, add_sub_right_comm, add_sub_assoc],
  exact is_positive.add hbc hab,
end

/-- `p ≤ q` means `q - p` is positive -/
@[refl, simp] lemma continuous_linear_map.is_positive.has_le
  {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [complete_space E] {p q : E →L[𝕜] E} :
  p ≤ q ↔ (q - p).is_positive :=
by refl

/-- saying `p` is positive is the same as saying `0 ≤ p` -/
@[refl, simp] lemma continuous_linear_map.is_positive.is_nonneg
  {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [complete_space E] {p : E →L[𝕜] E} :
  p.is_positive ↔ 0 ≤ p :=
begin
  nth_rewrite 0 ← sub_zero p,
  refl,
end

end

/-- a self-adjoint idempotent operator is positive -/
lemma self_adjoint_and_idempotent.is_positive {𝕜 E : Type*}
  [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E]
  {p : E →L[𝕜] E} (hp : is_idempotent_elem p) (hpa : is_self_adjoint p) :
  0 ≤ p :=
begin
  rw ← continuous_linear_map.is_positive.is_nonneg,
  refine ⟨hpa, _⟩,
  rw ← hp.eq,
  simp_rw [re_apply_inner_self_apply, mul_apply],
  intro x,
  simp_rw [← adjoint_inner_right _ _ x, is_self_adjoint_iff'.mp hpa],
  exact inner_self_nonneg,
end

/-- an idempotent is positive if and only if it is self-adjoint -/
lemma is_idempotent_elem.is_positive_iff_self_adjoint
  [inner_product_space 𝕜 E] [complete_space E]
  {p : E →L[𝕜] E} (hp : is_idempotent_elem p) :
  0 ≤ p ↔ is_self_adjoint p :=
⟨λ h, (continuous_linear_map.is_positive.is_nonneg.mpr h).1,
 λ h, self_adjoint_and_idempotent.is_positive hp h⟩

lemma is_idempotent_elem.self_adjoint_is_positive_is_orthogonal_projection_tfae
  {E : Type*} [normed_add_comm_group E] [inner_product_space ℂ E]
  [complete_space E] {p : E →L[ℂ] E} (hp : is_idempotent_elem p) :
  tfae [is_self_adjoint p, p.is_orthogonal_projection, 0 ≤ p] :=
begin
  tfae_have : 3 ↔ 1,
  { exact hp.is_positive_iff_self_adjoint, },
  tfae_have : 2 → 1,
  { intro h,
    rw [continuous_linear_map.is_orthogonal_projection,
      ← is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ hp] at h,
    exact h.2, },
  tfae_have : 1 → 2,
  { intros h,
    rw is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ hp at h,
    exact ⟨hp, h⟩, },
  tfae_finish,
end

/-- orthogonal projections are obviously positive -/
lemma orthogonal_projection.is_positive [inner_product_space ℂ E]
  {U : submodule ℂ E} [complete_space E] [complete_space U] :
  0 ≤ U.subtypeL.comp (P U) :=
self_adjoint_and_idempotent.is_positive (orthogonal_projection.idempotent U)
  (orthogonal_projection_is_self_adjoint U)

lemma self_adjoint_and_idempotent.sub_is_positive_of
  [inner_product_space 𝕜 E] [complete_space E] {p q : E →L[𝕜] E}
  (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)
  (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) (h : p.comp q = p) :
  0 ≤ q - p :=
self_adjoint_and_idempotent.is_positive
  (coe_inj.mp ((linear_map.commutes_iff_is_idempotent_elem (is_idempotent_elem.clm_to_lm.mp hp)
    (is_idempotent_elem.clm_to_lm.mp hq)).mp
   ⟨(coe_inj.mpr h), coe_inj.mpr ((self_adjoint_proj_commutes hpa hqa).mp h)⟩))
  (is_self_adjoint.sub hqa hpa)

/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then `Pᵤ(Pᵥ)=Pᵤ` implies `Pᵥ-Pᵤ` is positive (i.e., `Pᵤ ≤ Pᵥ`) -/
lemma orthogonal_projection.sub_is_positive_of [inner_product_space ℂ E] {U V : submodule ℂ E}
  [complete_space U] [complete_space V] [complete_space E]
  (h : (↥P U).comp (↥P V) = (↥P U)) :
  0 ≤ (↥P V) - (↥P U) :=
self_adjoint_and_idempotent.sub_is_positive_of
 (orthogonal_projection.idempotent U) (orthogonal_projection.idempotent V)
 (orthogonal_projection_is_self_adjoint U) (orthogonal_projection_is_self_adjoint V) h

/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then if `Pᵥ - Pᵤ` is idempotent, then `Pᵤ Pᵥ = Pᵤ` -/
lemma orthogonal_projection_commutes_of_is_idempotent [inner_product_space ℂ E]
  {U V : submodule ℂ E} [complete_space U] [complete_space V] [complete_space E]
  (h : is_idempotent_elem (↥P V - ↥P U)) :
  (↥P V).comp (↥P U) = (↥P U) :=
begin
  let p := ↥P U,
  let q := ↥P V,
  have pp : p = U.subtypeL.comp (P U) := rfl,
  have qq : q = V.subtypeL.comp (P V) := rfl,
  simp_rw [← pp, ← qq] at *,
  have hp : is_idempotent_elem p := orthogonal_projection.idempotent U,
  have hq : is_idempotent_elem q := orthogonal_projection.idempotent V,
  have hpa := orthogonal_projection_is_self_adjoint U,
  have hqa := orthogonal_projection_is_self_adjoint V,
  have h2 := self_adjoint_proj_commutes hpa hqa,
  exact coe_inj.mp ((linear_map.commutes_of_is_idempotent_elem (is_idempotent_elem.clm_to_lm.mp hp)
    (is_idempotent_elem.clm_to_lm.mp hq) (is_idempotent_elem.clm_to_lm.mp h)).2),
end

/-- copy of `linear_map.is_positive_iff_exists_adjoint_mul_self` -/
lemma continuous_linear_map.is_positive_iff_exists_adjoint_mul_self
  [inner_product_space 𝕜 E] [complete_space E]
  {n : ℕ} [finite_dimensional 𝕜 E] (hn : finite_dimensional.finrank 𝕜 E = n)
  (T : E →L[𝕜] E) :
  T.is_positive ↔ ∃ S : E →L[𝕜] E, T = S.adjoint * S :=
begin
  rw [← is_positive.to_linear_map,
    linear_map.is_positive_iff_exists_adjoint_mul_self _ hn, to_linear_map_eq_coe],
  split;
  rintros ⟨S, hS⟩;
  use S,
  { exact map_continuous S, },
  { simp_rw [continuous_linear_map.ext_iff, ← continuous_linear_map.coe_coe,
      ← continuous_linear_map.to_linear_map_eq_coe, ← linear_map.ext_iff] at *,
    exact hS, },
  { rw [hS, mul_def, coe_comp],
    refl, },
end

open is_R_or_C


/-- in a finite-dimensional complex Hilbert space `E`,
  if `p,q` are self-adjoint operators, then
  `p ≤ q` iff `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫` -/
lemma continuous_linear_map.is_positive_le_iff_inner
  {n : ℕ} [inner_product_space ℂ E] [finite_dimensional ℂ E]
  (hn : finite_dimensional.finrank ℂ E = n) {p q : E →L[ℂ] E}
  (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) :
  p ≤ q ↔ ∀ x : E, re ⟪x, p x⟫_ℂ ≤ re ⟪x, q x⟫_ℂ :=
begin
  rw [continuous_linear_map.is_positive.has_le],
  split,
  { intros h x,
    obtain ⟨S, hS⟩ := (continuous_linear_map.is_positive_iff_exists_adjoint_mul_self hn _).mp h,
    rw [← sub_nonneg, ← map_sub, ← inner_sub_right, ← sub_apply, hS, mul_apply,
        adjoint_inner_right],
    exact inner_self_nonneg, },
  { intros h,
    refine ⟨is_self_adjoint.sub hqa hpa, λ x, _⟩,
    simp_rw [re_apply_inner_self_apply, sub_apply, inner_sub_left,
             map_sub, sub_nonneg],
    nth_rewrite 0 inner_re_symm,
    nth_rewrite 1 inner_re_symm,
    exact h x, },
end

local notation `⟪` x `,` y `⟫` := @inner 𝕜 _ _ x y

/-- given self-adjoint idempotent operators `p,q`, we have
  `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫ ↔ ∀ x ∈ E, ‖p x‖ ≤ ‖q x‖` -/
lemma continuous_linear_map.has_le_norm
  [inner_product_space 𝕜 E] [complete_space E] {p q : E →L[𝕜] E}
  (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)
  (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) :
  (∀ x : E, re ⟪x, p x⟫ ≤ re ⟪x, q x⟫) ↔ ∀ x : E, ‖p x‖ ≤ ‖q x‖ :=
begin
  rw [← hp.eq, ← hq.eq],
  simp_rw [mul_apply, ← adjoint_inner_left _ (q _) _, ← adjoint_inner_left _ (p _) _,
    is_self_adjoint_iff'.mp hpa, is_self_adjoint_iff'.mp hqa, inner_self_eq_norm_sq,
    sq_le_sq, abs_norm, ← mul_apply, hp.eq, hq.eq, iff_self],
end

@[simp] lemma is_positive.has_le.sub [inner_product_space 𝕜 E]
  [complete_space E] {p q : E →L[𝕜] E} :
  p ≤ q ↔ 0 ≤ q - p :=
by refl

theorem self_adjoint_and_idempotent_is_positive_iff_commutes
  {n : ℕ} [inner_product_space ℂ E] [finite_dimensional ℂ E]
  (hn : finite_dimensional.finrank ℂ E = n) {p q : E →L[ℂ] E}
  (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)
  (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) :
  p ≤ q ↔ q.comp p = p :=
begin
  rw [← self_adjoint_proj_commutes hpa hqa, is_positive.has_le.sub],
  refine ⟨λ h, _,
          λ h, self_adjoint_and_idempotent.sub_is_positive_of hp hq hpa hqa h⟩,
  rw [← continuous_linear_map.is_positive.is_nonneg, ← continuous_linear_map.is_positive.has_le,
    (continuous_linear_map.is_positive_le_iff_inner hn hpa hqa)] at h,
  symmetry,
  rw ← sub_eq_zero,
  nth_rewrite 0 ← mul_one p,
  simp_rw [mul_def, ← comp_sub, ← continuous_linear_map.inner_map_self_eq_zero,
    comp_apply, sub_apply, one_apply],
  intros x,
  specialize h ((1 - q) x),
  simp_rw [sub_apply, map_sub, ← mul_apply, mul_one, hq.eq, sub_self,
    inner_zero_right, one_apply, mul_apply, ← map_sub, zero_re'] at h,
  rw [← hp.eq, mul_apply, ← adjoint_inner_left, is_self_adjoint_iff'.mp hpa,
    inner_self_nonpos] at h,
  rw [h, inner_zero_left],
end

/-- in a complex-finite-dimensional Hilbert space `E`, we have
  `Pᵤ ≤ Pᵤ` iff `PᵥPᵤ = Pᵤ` -/
theorem orthogonal_projection_is_le_iff_commutes
  {n : ℕ} [inner_product_space ℂ E]
  {U V : submodule ℂ E} [complete_space U] [complete_space V]
  [finite_dimensional ℂ E] (hn : finite_dimensional.finrank ℂ E = n) :
  ↥P U ≤ ↥P V
    ↔ (↥P V).comp (↥P U) = (↥P U) :=
self_adjoint_and_idempotent_is_positive_iff_commutes hn
  (orthogonal_projection.idempotent U) (orthogonal_projection.idempotent V)
  (orthogonal_projection_is_self_adjoint U) (orthogonal_projection_is_self_adjoint V)

lemma orthogonal_projection.is_le_iff_subset
  {n : ℕ} [inner_product_space ℂ E]
  {U V : submodule ℂ E} [complete_space U] [complete_space V] [finite_dimensional ℂ E]
  (hn : finite_dimensional.finrank ℂ E = n) :
  ↥P U ≤ ↥P V ↔ U ≤ V :=
by simp_rw [orthogonal_projection_is_le_iff_commutes hn, ← coe_inj, coe_comp,
  is_idempotent_elem.comp_idempotent_iff
    (is_idempotent_elem.clm_to_lm.mp (orthogonal_projection.idempotent V)),
  submodule.map_top, ← to_linear_map_eq_coe, range_to_linear_map,
  orthogonal_projection.range, iff_self]

lemma submodule.map_to_linear_map [module 𝕜 E] {p : E →L[𝕜] E} {U : submodule 𝕜 E} :
  submodule.map (p : E →ₗ[𝕜] E) U = submodule.map p U :=
rfl

/-- given self-adjoint idempotent operators `p,q` we have,
  `p(E) ⊆ q(E)` iff `q - p` is an idempotent operator -/
theorem continuous_linear_map.image_subset_iff_sub_of_is_idempotent
  [inner_product_space 𝕜 E] [complete_space E] {p q : E →L[𝕜] E}
  (hp : is_idempotent_elem p) (hq : is_idempotent_elem q)
  (hpa : is_self_adjoint p) (hqa : is_self_adjoint q) :
  (submodule.map p ⊤ ≤ submodule.map q ⊤) ↔ is_idempotent_elem (q - p) :=
by simp_rw [is_idempotent_elem.clm_to_lm, coe_sub,
  ← linear_map.commutes_iff_is_idempotent_elem (is_idempotent_elem.clm_to_lm.mp hp)
    (is_idempotent_elem.clm_to_lm.mp hq), ← coe_comp, coe_inj, self_adjoint_proj_commutes hpa hqa,
  and_self, ← coe_inj, coe_comp,
  is_idempotent_elem.comp_idempotent_iff (is_idempotent_elem.clm_to_lm.mp hq),
  submodule.map_to_linear_map, iff_self]

section min_proj

/-- definition of a map being a minimal projection -/
def continuous_linear_map.is_minimal_projection [inner_product_space 𝕜 E] [complete_space E]
  (x : E →L[𝕜] E) (U : submodule 𝕜 E) : Prop :=
is_self_adjoint x ∧ finite_dimensional.finrank 𝕜 U = 1 ∧ linear_map.is_proj U x

/-- definition of orthogonal projection being minimal
  i.e., when the dimension of its space equals one -/
def orthogonal_projection.is_minimal_projection [inner_product_space 𝕜 E] (U : submodule 𝕜 E)
  [complete_space U] : Prop :=
finite_dimensional.finrank 𝕜 U = 1

/-- given self-adjoint operators `p,q` we have
  `p = q` iff `p ≤ q` and `q ≤ p` -/
@[simp] lemma is_self_adjoint.has_le.le_antisymm_iff [inner_product_space 𝕜 E]
  [complete_space E] {p q : E →L[𝕜] E} (hp : is_self_adjoint p) (hq : is_self_adjoint q) :
  p = q ↔ p ≤ q ∧ q ≤ p :=
begin
  refine ⟨λ h, _, λ h, is_self_adjoint.has_le.le_antisymm hp hq h.1 h.2⟩,
  rw [h, and_self],
end

open finite_dimensional
/-- when a submodule `U` has dimension `1`, then
  for any submodule `V`, we have `V ≤ U` if and only if `V = U` or `V = 0` -/
lemma submodule.le_finrank_one [inner_product_space 𝕜 E]
  [finite_dimensional 𝕜 E] (U V : submodule 𝕜 E) (hU : finrank 𝕜 U = 1) :
  V ≤ U ↔ V = U ∨ V = 0 :=
begin
  simp_rw [submodule.zero_eq_bot],
  split,
  { intros h,
    have : finrank 𝕜 V ≤ 1,
    { rw ← hU,
      apply submodule.finrank_le_finrank_of_le h, },
    have : finrank 𝕜 V = 0 ∨ finrank 𝕜 V = 1,
    { exact order.le_succ_bot_iff.mp this, },
    cases this,
    { simp only [finrank_eq_zero] at this_1,
      right,
      exact this_1, },
    { left,
      apply eq_of_le_of_finrank_eq h,
      simp_rw [this_1, hU], }, },
    { intros h,
      rcases h with ⟨rfl, rfl⟩,
      { exact le_refl U, },
      { rw h,
        exact bot_le, }, },
end

/-- for orthogonal projections `Pᵤ,Pᵥ`,
  if `Pᵤ` is a minimal orthogonal projection, then
  for any `Pᵥ` if `Pᵥ ≤ Pᵤ` and `Pᵥ ≠ 0`, then `Pᵥ = Pᵤ` -/
lemma orthogonal_projection.is_minimal_projection_of
  {n : ℕ} [inner_product_space ℂ E] [finite_dimensional ℂ E] (hn : finrank ℂ E = n)
  (U W : submodule ℂ E) (hU : orthogonal_projection.is_minimal_projection U)
  (hW : ↥P W ≤ ↥P U) (h : ↥P W ≠ 0) :
  ↥P W = ↥P U :=
begin
  simp_rw [orthogonal_projection'_eq, is_self_adjoint.has_le.le_antisymm_iff
    (orthogonal_projection_is_self_adjoint W) (orthogonal_projection_is_self_adjoint U),
    ← orthogonal_projection'_eq],
  refine ⟨hW, _⟩,
  rw orthogonal_projection.is_le_iff_subset hn at hW ⊢,
  have := submodule.finrank_le_finrank_of_le hW,
  simp_rw [orthogonal_projection.is_minimal_projection] at hU,
  rw submodule.le_finrank_one U W hU at hW,
  cases hW with hW1 hW2,
  { simp_rw [hW1, le_refl], },
  { simp_rw [hW2, submodule.zero_eq_bot, orthogonal_projection'_eq,
      orthogonal_projection_bot, comp_zero] at h,
    contradiction, },
end

/-- any rank one operator given by a norm one vector is a minimal projection -/
lemma rank_one.is_minimal_projection [inner_product_space ℂ E] [complete_space E]
  (x : E) (h : ‖x‖ = 1) :
  (rank_one x x).is_minimal_projection (submodule.span ℂ {x}) :=
begin
  refine ⟨rank_one.is_self_adjoint x, _⟩,
  simp_rw [finrank_eq_one_iff'],
  split,
  { use ⟨x, submodule.mem_span_singleton_self x⟩,
    simp_rw [ne.def, submodule.mk_eq_zero, set_like.mk_smul_mk],
    refine ⟨norm_ne_zero_iff.mp (by { rw h, exact one_ne_zero, } ), λ w, _⟩,
    cases submodule.mem_span_singleton.mp (set_like.coe_mem w) with r hr,
    use r,
    simp_rw [hr, set_like.eta], },
  { apply linear_map.is_proj.mk,
    simp_rw [submodule.mem_span_singleton, rank_one_apply, exists_apply_eq_apply, forall_const],
    simp_rw [submodule.mem_span_singleton, rank_one_apply, forall_exists_index,
      forall_apply_eq_imp_iff', inner_smul_right, inner_self_eq_norm_sq_to_K,
      h, complex.of_real_one, one_pow, mul_one, eq_self_iff_true, forall_const], },
end

/-- if `x ∈ E` then we can normalize this (i.e., there exists `y ∈ E`
  such that `∥y∥ = 1` where `x = r • y` for some `r ∈ ℝ`) unless `x = 0` -/
lemma normalize_op [inner_product_space ℂ E] (x : E) :
  (∃ (y : E) (r : ℝ), ‖y‖ = 1 ∧ x = (r : ℂ) • y) ∨ (x = 0) :=
begin
 by_cases A : x = 0,
 { right,
   exact A },
 { have B : ‖x‖ ≠ 0 := by { simp only [ne.def, norm_eq_zero],
                            exact A, },
   use (1 / ‖x‖) • x,
   use ‖x‖,
   split,
   { simp_rw [norm_smul, one_div, norm_inv, norm_norm, mul_comm, mul_inv_cancel B], },
   { simp_rw [one_div, complex.coe_smul, smul_inv_smul₀ B], }, },
end

/-- given any non-zero `x ∈ E`, we have
  `1 / ‖x‖ ^ 2 • |x⟩⟨x|` is a minimal projection -/
lemma rank_one.is_minimal_projection' [inner_product_space ℂ E] [complete_space E]
  (x : E) (h : x ≠ 0) :
  ((1 / ‖x‖ ^ 2) • rank_one x x).is_minimal_projection (submodule.span ℂ {x}) :=
begin
  rcases normalize_op x with ⟨y, r, ⟨hy, hx⟩⟩,
  { have : r ^ 2 ≠ 0,
    { intros d,
      rw [pow_eq_zero_iff (two_pos)] at d,
      rw [d, complex.coe_smul, zero_smul] at hx,
      contradiction,
      exact is_right_cancel_mul_zero.to_no_zero_divisors ℝ, },
    simp_rw [hx, complex.coe_smul, one_div, ← complex.coe_smul, rank_one.apply_smul,
      rank_one.smul_real_apply, norm_smul, mul_pow, complex.norm_real, mul_inv, smul_smul, hy,
      one_pow, inv_one, mul_one, real.norm_eq_abs, ← abs_pow, pow_two, abs_mul_self, ← pow_two,
      complex.of_real_inv, complex.of_real_pow, complex.coe_smul],
    norm_cast,
    rw [inv_mul_cancel this, one_smul],
    have : submodule.span ℂ {↑r • y} = submodule.span ℂ {y},
    { rw submodule.span_singleton_smul_eq _,
      refine ne.is_unit _,
      exact coe_to_lift,
      rw ne.def,
      rw ← pow_eq_zero_iff (two_pos),
      norm_cast,
      exact this,
      exact lex.no_zero_divisors, },
    rw [← complex.coe_smul, this],
    exact rank_one.is_minimal_projection y hy, },
  { contradiction, }
end

/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is self-adjoint and idempotent;
  so it always suffices to say `p = p⋆ = p²` -/
lemma orthogonal_projection_iff [inner_product_space 𝕜 E]
  [complete_space E] [finite_dimensional 𝕜 E] {p : E →L[𝕜] E} :
  (∃ U : submodule 𝕜 E, ↥P U = p) ↔ (is_self_adjoint p ∧ is_idempotent_elem p) :=
begin
  split,
  { rintros ⟨U, hp⟩,
    rw ← hp,
    exact ⟨orthogonal_projection_is_self_adjoint _, orthogonal_projection.idempotent _⟩, },
  { rintros ⟨h1, h2⟩,
    simp_rw [is_idempotent_elem, mul_def, continuous_linear_map.ext_iff,
      ← continuous_linear_map.coe_coe, coe_comp, ← linear_map.ext_iff] at h2,
    rcases (linear_map.is_proj_iff_idempotent _).mpr h2 with ⟨W, hp⟩,
    let p' := is_proj' hp,
    have hp' : p' = is_proj' hp := rfl,
    simp_rw [continuous_linear_map.ext_iff, ← continuous_linear_map.coe_coe, ← is_proj'_apply hp,
      orthogonal_projection'_eq_linear_proj', ← hp'],
    rw ← linear_map.linear_proj_of_is_compl_of_proj p' (is_proj'_eq hp),
    use W,
    intros x,
    simp_rw [linear_map.coe_comp, submodule.coe_subtype, set_like.coe_eq_coe],
    suffices : p'.ker = Wᗮ,
    { simp_rw this, },
    ext y,
    simp_rw [linear_map.mem_ker, submodule.mem_orthogonal],
    split,
    { intros hp'y u hu,
      rw [← hp.2 u hu, continuous_linear_map.coe_coe, ← adjoint_inner_right,
        is_self_adjoint.adjoint_eq h1, ← continuous_linear_map.coe_coe,
        ← is_proj'_apply hp, ← hp', hp'y, submodule.coe_zero, inner_zero_right], },
    { intros h,
      rw [← submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, is_proj'_apply hp,
        continuous_linear_map.coe_coe, ← adjoint_inner_left, is_self_adjoint.adjoint_eq h1,
        ← continuous_linear_map.coe_coe, ← linear_map.comp_apply, h2,
        h _ (linear_map.is_proj.map_mem hp _)], }, },
end

/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is a self-adjoint linear projection onto the submodule;
  also see `orthogonal_projection_iff` -/
lemma orthogonal_projection_iff' [inner_product_space 𝕜 E]
  [complete_space E] [finite_dimensional 𝕜 E] {p : E →L[𝕜] E} (U : submodule 𝕜 E) :
  ↥P U = p ↔ (is_self_adjoint p ∧ linear_map.is_proj U p) :=
begin
  split,
  { intros h,
    rw ← h,
    refine ⟨orthogonal_projection_is_self_adjoint _, _⟩,
    apply linear_map.is_proj.mk,
    simp_rw [orthogonal_projection'_apply, submodule.coe_mem, forall_const],
    simp_rw [orthogonal_projection'_apply, orthogonal_projection_eq_self_iff, imp_self,
      forall_const], },
  { rintros ⟨h, h2⟩,
    have : p.comp p = p,
    { simp_rw [continuous_linear_map.ext_iff, ← continuous_linear_map.coe_coe,
        continuous_linear_map.coe_comp, ← linear_map.ext_iff, ← linear_map.is_proj_iff_idempotent],
      use U,
      apply linear_map.is_proj.mk;
      simp_rw [continuous_linear_map.coe_coe],
      exact h2.1,
      exact h2.2, },
    have hp : linear_map.is_proj U (p : E →ₗ[𝕜] E),
    { apply linear_map.is_proj.mk;
      simp_rw [continuous_linear_map.coe_coe],
      exact h2.1,
      exact h2.2, },
    simp_rw [continuous_linear_map.ext_iff, ← continuous_linear_map.coe_coe,
      orthogonal_projection'_eq_linear_proj'],
    let p' := is_proj' hp,
    have hp' : p' = is_proj' hp := rfl,
    simp_rw [← is_proj'_apply hp, ← hp'],
    rw ← linear_map.linear_proj_of_is_compl_of_proj p' (is_proj'_eq hp),
    simp_rw [linear_map.coe_comp, submodule.coe_subtype, set_like.coe_eq_coe],
    intros x,
    suffices : p'.ker = Uᗮ,
    { simp_rw this, },
    ext y,
    simp_rw [linear_map.mem_ker, submodule.mem_orthogonal],
    split,
    { intros hp'y u hu,
      rw [← hp.2 u hu, continuous_linear_map.coe_coe, ← adjoint_inner_right,
        is_self_adjoint.adjoint_eq h, ← continuous_linear_map.coe_coe,
        ← is_proj'_apply hp, ← hp', hp'y, submodule.coe_zero, inner_zero_right], },
    { intros h',
      rw [← submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, is_proj'_apply hp,
        continuous_linear_map.coe_coe, ← adjoint_inner_left, is_self_adjoint.adjoint_eq h,
        ← continuous_linear_map.comp_apply, this, h' _ (linear_map.is_proj.map_mem h2 _)], }, },
end

lemma orthogonal_projection.is_minimal_projection_to_clm [inner_product_space 𝕜 E]
  (U : submodule 𝕜 E) [complete_space E] [finite_dimensional 𝕜 E] :
  (↥P U).is_minimal_projection U ↔ orthogonal_projection.is_minimal_projection U :=
begin
  refine ⟨λ h, h.2.1, λ h, _⟩,
  rw [continuous_linear_map.is_minimal_projection, and.left_comm, ← orthogonal_projection_iff' U],
  refine ⟨h, _⟩,
  refl,
end

lemma submodule.is_ortho_iff_inner_eq' {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] {U W : submodule 𝕜 E} :
  U ⟂ W ↔ ∀ (u : ↥U) (w : ↥W), (inner (u : E) (w : E) : 𝕜) = 0 :=
begin
  rw [submodule.is_ortho_iff_inner_eq],
  split,
  { intros h u w,
    exact h _ (set_like.coe_mem _) _ (set_like.coe_mem _), },
  { intros h x hx y hy,
    exact h ⟨x, hx⟩ ⟨y, hy⟩, },
end

-- moved from `ips.lean`
/-- `U` and `W` are mutually orthogonal if and only if `(P U).comp (P W) = 0`,
where `P U` is `orthogonal_projection U` -/
lemma submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero
  [inner_product_space 𝕜 E] (U W : submodule 𝕜 E) [complete_space U] [complete_space W] :
  U ⟂ W ↔ (↥P U).comp (↥P W) = 0 :=
begin
  rw submodule.is_ortho_iff_inner_eq',
  split,
  { intros h,
    ext v,
    rw [continuous_linear_map.comp_apply, continuous_linear_map.zero_apply,
      ← @inner_self_eq_zero 𝕜, orthogonal_projection'_apply, orthogonal_projection'_apply,
      ← inner_orthogonal_projection_left_eq_right,orthogonal_projection_mem_subspace_eq_self],
    exact h _ _,
     },
  { intros h x y,
    rw [← orthogonal_projection_eq_self_iff.mpr (set_like.coe_mem x),
      ← orthogonal_projection_eq_self_iff.mpr (set_like.coe_mem y),
      inner_orthogonal_projection_left_eq_right, ← orthogonal_projection'_apply,
      ← orthogonal_projection'_apply, ← continuous_linear_map.comp_apply, h,
      continuous_linear_map.zero_apply, inner_zero_right], },
end
--

lemma orthogonal_projection.orthogonal_complement_eq [inner_product_space 𝕜 E] [complete_space E]
  (U : submodule 𝕜 E) [complete_space ↥U] :
  ↥P Uᗮ = 1 - ↥P U :=
begin
  have : 1 = id 𝕜 E := rfl,
  simp_rw [this, id_eq_sum_orthogonal_projection_self_orthogonal_complement U,
    orthogonal_projection'_eq, add_sub_cancel'],
end

example {n : ℕ} [inner_product_space ℂ E] [finite_dimensional ℂ E]
  {U W : submodule ℂ E} (h : finrank ℂ E = n) :
  (↥P U).comp (↥P W) = 0 ↔ (↥P U) + (↥P W) ≤ 1 :=
begin
  simp_rw [← submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero,
    submodule.is_ortho_iff_le, ← orthogonal_projection.is_le_iff_subset h,
    orthogonal_projection.orthogonal_complement_eq, add_comm (↥P U) (↥P W),
    has_le.le, sub_add_eq_sub_sub, iff_self],
end

end min_proj
