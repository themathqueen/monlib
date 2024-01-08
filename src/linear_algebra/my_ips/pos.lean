/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.spectrum
import linear_algebra.my_ips.rank_one
import linear_algebra.End
import analysis.inner_product_space.positive
import preq.is_R_or_C_le

/-!

# Positive linear maps

This file generalises the notion of positivity to linear maps. We follow the same definition as `continuous_linear_map.is_positive` but change the `self-adjoinnt` property to `is_symmertric`, i.e., a linear map is positive if it is symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

for linear maps:
* `linear_map.is_positive.conj_adjoint` : if `T : E →ₗ[𝕜] E` and `E` is a finite-dimensional space,
  then for any `S : E →ₗ[𝕜] F`, we have `S.comp (T.comp S.adjoint)` is also positive.

-/

/-- set over `K` is **non-negative** if all its elements are non-negative -/
def set.is_nonneg {K : Type*} [has_le K] [has_zero K]
  (A : set K) : Prop :=
∀ x : K, x ∈ A → 0 ≤ x

open inner_product_space is_R_or_C
open_locale inner_product complex_conjugate
variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_add_comm_group F]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y


namespace linear_map

/-- `T` is (semi-definite) **positive** if `T` is symmetric
and `∀ x : V, 0 ≤ re ⟪x, T x⟫` -/
def is_positive (T : E →ₗ[𝕜] E) : Prop :=
T.is_symmetric ∧ ∀ x : E, 0 ≤ re ⟪x, T x⟫

lemma is_positive_zero : (0 : E →ₗ[𝕜] E).is_positive :=
begin
  refine ⟨is_symmetric_zero, λ x, _⟩,
  simp_rw [zero_apply, inner_re_zero_right],
end

lemma is_positive_one : (1 : E →ₗ[𝕜] E).is_positive :=
⟨is_symmetric_id, λ x, inner_self_nonneg⟩

lemma is_positive.add {S T : E →ₗ[𝕜] E} (hS : S.is_positive) (hT : T.is_positive) :
  (S + T).is_positive :=
begin
  refine ⟨is_symmetric.add hS.1 hT.1, λ x, _⟩,
  rw [add_apply, inner_add_right, map_add],
  exact add_nonneg (hS.2 _) (hT.2 _),
end

lemma is_positive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪T x, x⟫ :=
by { rw inner_re_symm, exact hT.2 x, }

lemma is_positive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪x, T x⟫ :=
hT.2 x

/-- a linear projection onto `U` along its complement `V` is positive if
and only if `U` and `V` are pairwise orthogonal -/
lemma linear_proj_is_positive_iff {U V : submodule 𝕜 E} (hUV : is_compl U V) :
  (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_positive ↔ U ⟂ V :=
begin
  split,
  { intros h u hu v hv,
    rw [← subtype.coe_mk u hu, ← subtype.coe_mk v hv,
        ← submodule.linear_proj_of_is_compl_apply_left hUV ⟨u, hu⟩,
        ← submodule.subtype_apply U, ← comp_apply, ← h.1 _ _,
        comp_apply, submodule.linear_proj_of_is_compl_apply_right hUV ⟨v, hv⟩,
        map_zero, inner_zero_left], },
  { intro h,
    have : (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_symmetric,
    { intros x y,
      nth_rewrite 0 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV y,
      nth_rewrite 1 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV x,
      rw submodule.is_ortho_iff_inner_eq at h,
      simp_rw [inner_add_right, inner_add_left, comp_apply,
        submodule.subtype_apply _, h (_ : E) (set_like.coe_mem _) (_ : E) (set_like.coe_mem _),
        inner_eq_zero_symm.mp (h _ (set_like.coe_mem _) _ (set_like.coe_mem _))], },
    refine ⟨this, _⟩,
    intros x,
    rw [comp_apply, submodule.subtype_apply,
        ← submodule.linear_proj_of_is_compl_idempotent,
        ← submodule.subtype_apply, ← comp_apply,
        ← this _ ((U.linear_proj_of_is_compl V hUV) x)],
    exact inner_self_nonneg, },
end

section finite_dimensional

local notation `e` := is_symmetric.eigenvector_basis
local notation `α` := is_symmetric.eigenvalues
local notation `√` := real.sqrt

variables {n : ℕ} [finite_dimensional 𝕜 E] (T : E →ₗ[𝕜] E)

open_locale complex_order

/-- the spectrum of a positive linear map is non-negative -/
lemma is_positive.nonneg_spectrum (h : T.is_positive) :
  (spectrum 𝕜 T).is_nonneg :=
begin
  cases h with hT h,
  intros μ hμ,
  simp_rw [← module.End.has_eigenvalue_iff_mem_spectrum] at hμ,
  have : ↑(re μ) = μ,
  { simp_rw [← conj_eq_iff_re],
    exact is_symmetric.conj_eigenvalue_eq_self hT hμ, },
  rw ← this at hμ,
  rw [is_R_or_C.nonneg_def'],
  exact ⟨this, eigenvalue_nonneg_of_nonneg hμ h⟩,
end

open_locale big_operators
/-- given a symmetric linear map with a non-negative spectrum,
we can write `T x = ∑ i, √α i • √α i • ⟪e i, x⟫` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`is_symmetric.eigenvector_basis`) -/
lemma sq_mul_sq_eq_self_of_is_symmetric_and_nonneg_spectrum
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric)
  (hT1 : (spectrum 𝕜 T).is_nonneg) (v : E) :
  T v = ∑ i, ((√ (α hT hn i) • √ (α hT hn i)) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i :=
begin
  have : ∀ i : fin n, 0 ≤ α hT hn i := λ i,
  by { specialize hT1 (hT.eigenvalues hn i),
       simp only [zero_le_real, of_real_re, eq_self_iff_true, true_and] at hT1,
       apply hT1 (module.End.mem_spectrum_of_has_eigenvalue
         (is_symmetric.has_eigenvalue_eigenvalues hT hn i)), },
  calc T v = ∑ i, ⟪e hT hn i, v⟫ • T (e hT hn i) : _
       ... = ∑ i, ((√ (α hT hn i) • √ (α hT hn i)) : 𝕜) • ⟪e hT hn i, v⟫ • (e hT hn i) : _,
  simp_rw [← orthonormal_basis.repr_apply_apply, ← map_smul_of_tower, ← linear_map.map_sum,
    orthonormal_basis.sum_repr (e hT hn) v, is_symmetric.apply_eigenvector_basis,
    smul_smul, real_smul_of_real, ← of_real_mul, ← real.sqrt_mul (this _),
    real.sqrt_mul_self (this _), mul_comm],
end

/-- given a symmetric linear map `T` and a real number `r`,
we can define a linear map `S` such that `S = T ^ r` -/
noncomputable def re_pow [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (hT : T.is_symmetric) (r : ℝ) : E →ₗ[𝕜] E :=
{ to_fun := λ v, ∑ i : fin n, ((((α hT hn i : ℝ) ^ r : ℝ)) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i,
  map_add' := λ x y, by simp_rw [inner_add_right, add_smul, smul_add, finset.sum_add_distrib],
  map_smul' := λ r x, by simp_rw [inner_smul_right, ← smul_smul, finset.smul_sum,
    ring_hom.id_apply, smul_smul, ← mul_assoc, mul_comm] }

section

noncomputable def cpow [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [decidable_eq ℂ] (hn : finite_dimensional.finrank ℂ E = n) (T : E →ₗ[ℂ] E)
  (hT : T.is_positive) (c : ℂ) :
  E →ₗ[ℂ] E :=
{ to_fun := λ v, ∑ i : fin n, ((α hT.1 hn i) ^ c : ℂ) • ⟪e hT.1 hn i, v⟫_ℂ • e hT.1 hn i,
  map_add' := λ x y, by simp_rw [inner_add_right, add_smul, smul_add, finset.sum_add_distrib],
  map_smul' := λ r x, by simp_rw [inner_smul_right, ← smul_smul, finset.smul_sum,
                                  ring_hom.id_apply, smul_smul, ← mul_assoc, mul_comm] }

lemma cpow_apply [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [decidable_eq ℂ] (hn : finite_dimensional.finrank ℂ E = n) (T : E →ₗ[ℂ] E)
  (hT : T.is_positive) (c : ℂ) (v : E) :
  T.cpow hn hT c v = ∑ i : fin n, ((α hT.1 hn i) ^ c : ℂ) • ⟪e hT.1 hn i, v⟫_ℂ • e hT.1 hn i :=
rfl
end

lemma re_pow_apply [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (hT : T.is_symmetric) (r : ℝ) (v : E) :
  T.re_pow hn hT r v = ∑ i : fin n, (((α hT hn i : ℝ) ^ r : ℝ) : 𝕜) • ⟪e hT hn i, v⟫ • e hT hn i :=
rfl

/-- the square root of a symmetric linear map can then directly be defined with `re_pow` -/
noncomputable def sqrt [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n)
  (h : T.is_symmetric) :
  E →ₗ[𝕜] E := T.re_pow hn h (1 / 2 : ℝ)

/-- the square root of a symmetric linear map `T`
is written as `T x = ∑ i, √ (α i) • ⟪e i, x⟫ • e i` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`is_symmetric.eigenvector_basis`) -/
lemma sqrt_apply (hn : finite_dimensional.finrank 𝕜 E = n) [decidable_eq 𝕜]
  (hT : T.is_symmetric) (x : E) :
  T.sqrt hn hT x = ∑ i, (√ (α hT hn i) : 𝕜) • ⟪e hT hn i, x⟫ • e hT hn i :=
by { simp_rw [real.sqrt_eq_rpow _], refl }

/-- given a symmetric linear map `T` with a non-negative spectrum,
the square root of `T` composed with itself equals itself, i.e., `T.sqrt ^ 2 = T`  -/
lemma sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric)
  (hT1 : (spectrum 𝕜 T).is_nonneg) :
  (T.sqrt hn hT) ^ 2 = T :=
by simp_rw [pow_two, mul_eq_comp, linear_map.ext_iff, comp_apply, sqrt_apply,
            inner_sum, inner_smul_real_right, smul_smul, inner_smul_right,
            ← orthonormal_basis.repr_apply_apply, orthonormal_basis.repr_self,
            euclidean_space.single_apply, mul_boole, smul_ite, smul_zero,
            finset.sum_ite_eq, finset.mem_univ, if_true, algebra.mul_smul_comm,
            sq_mul_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn hT hT1,
            orthonormal_basis.repr_apply_apply, ← smul_eq_mul, ← smul_assoc,
            eq_self_iff_true, forall_const]

/-- given a symmetric linear map `T`, we have that its root is positive -/
lemma is_symmetric.sqrt_is_positive
  [decidable_eq 𝕜] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_symmetric) :
  (T.sqrt hn hT).is_positive :=
begin
  have : (T.sqrt hn hT).is_symmetric,
  { intros x y,
    simp_rw [sqrt_apply T hn hT, inner_sum, sum_inner, smul_smul, inner_smul_right,
      inner_smul_left],
    have : ∀ i : fin n, conj ((√ (α hT hn i)) : 𝕜) = ((√ (α hT hn i)) : 𝕜) := λ i,
    by simp_rw [conj_eq_iff_re, of_real_re],
    simp_rw  [mul_assoc, map_mul, this _, inner_conj_symm, mul_comm ⟪e hT hn _, y⟫ _,
      ← mul_assoc], },
  refine ⟨this, _⟩,
  intro x,
  simp_rw [sqrt_apply _ hn hT, inner_sum, add_monoid_hom.map_sum, inner_smul_right],
  apply finset.sum_nonneg',
  intros i,
  simp_rw [← inner_conj_symm x _, ← orthonormal_basis.repr_apply_apply, mul_conj,
    ← of_real_mul, of_real_re],
  exact mul_nonneg (real.sqrt_nonneg _) (norm_sq_nonneg _),
end

/-- `T` is positive if and only if `T` is symmetric
(which is automatic from the definition of positivity)
and has a non-negative spectrum -/
lemma is_positive_iff_is_symmetric_and_nonneg_spectrum
  (hn : finite_dimensional.finrank 𝕜 E = n) :
  T.is_positive ↔ T.is_symmetric ∧ (spectrum 𝕜 T).is_nonneg :=
begin
  classical,
  refine ⟨λ h, ⟨h.1, λ μ hμ, is_positive.nonneg_spectrum T h μ hμ⟩, λ h, ⟨h.1, _⟩⟩,
  intros x,
  rw [← sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn h.1 h.2,
    pow_two, mul_apply, ← adjoint_inner_left, is_self_adjoint_iff'.mp
      ((is_symmetric_iff_is_self_adjoint _).mp (is_symmetric.sqrt_is_positive T hn h.1).1)],
  exact inner_self_nonneg,
end

/-- `T` is positive if and only if there exists a
linear map `S` such that `T = S.adjoint * S` -/
lemma is_positive_iff_exists_adjoint_mul_self
  (hn : finite_dimensional.finrank 𝕜 E = n) :
  T.is_positive ↔ ∃ S : E →ₗ[𝕜] E, T = S.adjoint * S :=
begin
  classical,
   split,
  { rw [is_positive_iff_is_symmetric_and_nonneg_spectrum T hn],
    rintro ⟨hT, hT1⟩,
    use T.sqrt hn hT,
    rw [is_self_adjoint_iff'.mp ((is_symmetric_iff_is_self_adjoint _).mp
        (is_symmetric.sqrt_is_positive T hn hT).1), ← pow_two],
    exact (sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum T hn hT hT1).symm, },
  { intros h,
    rcases h with ⟨S, rfl⟩,
    refine ⟨is_symmetric_adjoint_mul_self S, _⟩,
    intro x,
    simp_rw [mul_apply, adjoint_inner_right],
    exact inner_self_nonneg, },
end

section complex

/-- for spaces `V` over `ℂ`, it suffices to define positivity with
`0 ≤ ⟪v, T v⟫_ℂ` for all `v ∈ V` -/
lemma complex_is_positive {V : Type*} [normed_add_comm_group V]
  [inner_product_space ℂ V] (T : V →ₗ[ℂ] V) :
  T.is_positive ↔ ∀ v : V, ↑(re ⟪v, T v⟫_ℂ) = ⟪v, T v⟫_ℂ ∧ 0 ≤ re ⟪v, T v⟫_ℂ :=
by simp_rw [is_positive, is_symmetric_iff_inner_map_self_real, inner_conj_symm,
  ← conj_eq_iff_re, inner_conj_symm, ← forall_and_distrib, and_comm, eq_comm]

end complex

lemma is_positive.conj_adjoint [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : E →ₗ[𝕜] F) (h : T.is_positive) :
  (S.comp (T.comp S.adjoint)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, ← adjoint_inner_left _ (T _), ← adjoint_inner_right _ (T _) _],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, ← adjoint_inner_left _ (T _)],
  exact h.2 _,
end

lemma is_positive.adjoint_conj [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : F →ₗ[𝕜] E) (h : T.is_positive) :
  (S.adjoint.comp (T.comp S)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, adjoint_inner_left, adjoint_inner_right],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, adjoint_inner_right],
  exact h.2 _,
end

variable (hn : finite_dimensional.finrank 𝕜 E = n)
local notation `√T⋆`T := (T.adjoint.comp T).sqrt hn (is_symmetric_adjoint_mul_self T)

/-- we have `(T.adjoint.comp T).sqrt` is positive, given any linear map `T` -/
lemma sqrt_adjoint_self_is_positive [decidable_eq 𝕜] (T : E →ₗ[𝕜] E) : (√T⋆T).is_positive :=
is_symmetric.sqrt_is_positive _ hn (is_symmetric_adjoint_mul_self T)

/-- given any linear map `T` and `x ∈ E` we have
`‖(T.adjoint.comp T).sqrt x‖ = ‖T x‖` -/
lemma norm_of_sqrt_adjoint_mul_self_eq [decidable_eq 𝕜] (T : E →ₗ[𝕜] E) (x : E) :
  ‖(√T⋆T) x‖ = ‖T x‖ :=
begin
simp_rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), ← @inner_self_eq_norm_sq 𝕜,
  ← adjoint_inner_left, is_self_adjoint_iff'.mp
    ((is_symmetric_iff_is_self_adjoint _).mp (sqrt_adjoint_self_is_positive hn T).1),
  ← mul_eq_comp, ← mul_apply, ← pow_two, mul_eq_comp],
 congr,
 apply sqrt_sq_eq_self_of_is_symmetric_and_nonneg_spectrum,
 apply is_positive.nonneg_spectrum _ ⟨is_symmetric_adjoint_mul_self T, _⟩,
 intros x,
 simp_rw [mul_apply, adjoint_inner_right],
 exact inner_self_nonneg,
end

lemma invertible_iff_inner_map_self_pos (hn : finite_dimensional.finrank 𝕜 E = n)
  (hT : T.is_positive) :
  function.bijective T ↔ ∀ v : E, v ≠ 0 → 0 < re ⟪T v, v⟫ :=
begin
  split,
  { intros h v hv,
    cases (is_positive_iff_exists_adjoint_mul_self T hn).mp hT with S hS,
    rw [hS, mul_apply, adjoint_inner_left, inner_self_eq_norm_sq],
    suffices : S v ≠ 0,
    { rw ← norm_ne_zero_iff at this,
      exact (sq_pos_iff ‖S v‖).mpr this, },
    by_contra',
    rw ext_iff at hS,
    specialize hS v,
    rw [mul_apply, this, map_zero] at hS,
    apply hv,
    apply_fun T,
    rw map_zero,
    exact hS,
    exact h.1, },
  { intros h,
    by_contra',
    rw [function.bijective, ← injective_iff_surjective, and_self, injective_iff_map_eq_zero] at this,
    push_neg at this,
    cases this with a ha,
    specialize h a ha.2,
    rw [ha.1, inner_zero_left, zero_re', lt_self_iff_false] at h,
    exact h, }
end

lemma ext_inner_left_iff [inner_product_space 𝕜 E] (x y : E) :
  x = y ↔ ∀ v : E, ⟪x, v⟫ = ⟪y, v⟫ :=
begin
  split,
  { intros h v,
    simp_rw h, },
  { rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero],
    intros h, exact h _, }
end

lemma invertible_pos (T : E →ₗ[𝕜] E)
  [invertible T] (hn : finite_dimensional.finrank 𝕜 E = n) (hT : T.is_positive) :
  is_positive (⅟ T) :=
begin
  have : function.bijective T,
  { refine (module.End_is_unit_iff T).mp _,
    exact is_unit_of_invertible T, },
  have t1 := this,
  rw invertible_iff_inner_map_self_pos T hn hT at this,
  split,
  { intros u v,
    rw ← adjoint_inner_left,
    revert v,
    have t : (⅟ T).adjoint = ⅟ T.adjoint := rfl,
    have ugh := is_self_adjoint_iff'.mp ((is_symmetric_iff_is_self_adjoint T).mp hT.1),
    have hmm : invertible T.adjoint,
    { rw ugh, exact _inst_7, },
    rw ← ext_inner_left_iff ((⅟ T) u) ((⅟ T).adjoint u),
    rw t,
    apply_fun (T.adjoint : E →ₗ[𝕜] E),
    simp_rw ← mul_apply,
    rw [mul_inv_of_self, one_apply, mul_apply],
    rw ext_iff at ugh,
    specialize ugh ((⅟ T) u),
    nth_rewrite 1 ← mul_apply at ugh,
    rw [mul_inv_of_self, one_apply] at ugh,
    exact ugh,
    rw ugh,
    exact t1.1, exact _inst_4, exact _inst_6, },
  { intro x,
    by_cases b : ⅟ T x = 0,
    { rw [b, inner_zero_right, map_zero], },
    { specialize this _ b,
      rw [← mul_apply, mul_inv_of_self, one_apply] at this,
      exact le_of_lt this, }, },
end

lemma is_symmetric.re_pow_eq_rank_one {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  [decidable_eq 𝕜] {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)
  {T : E →ₗ[𝕜] E} (hT : T.is_symmetric) (r : ℝ) :
  linear_map.re_pow T hn hT r = ∑ i, (((hT.eigenvalues hn i) ^ r : ℝ) : 𝕜)
    • @rank_one 𝕜 E _ _ _ (hT.eigenvector_basis hn i) (hT.eigenvector_basis hn i) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.re_pow_apply, linear_map.sum_apply,
    linear_map.smul_apply, continuous_linear_map.coe_coe],
  intros,
  refl,
end

lemma is_symmetric.invertible (hT : T.is_symmetric) [invertible T] :
  (⅟ T).is_symmetric :=
begin
  rw [linear_map.is_symmetric_iff_is_self_adjoint, is_self_adjoint_iff] at ⊢ hT,
  simp_rw [star_inv_of],
  simp only [hT, inv_of_inj],
end

lemma is_positive_and_invertible_pos_eigenvalues (hT : T.is_positive) [invertible T]
  [decidable_eq 𝕜] (i : fin n) :
  0 < hT.1.eigenvalues hn i :=
begin
  -- have := linear_map.invertible_pos T hn hT,
  -- have fs : function.bijective ⇑(⅟ T),
  have fs : function.bijective ⇑T,
  { rw function.bijective_iff_has_inverse,
    use ⇑(⅟ T),
    simp_rw [function.right_inverse, function.left_inverse, ← linear_map.mul_apply,
      inv_of_mul_self, mul_inv_of_self, linear_map.one_apply, and_self, eq_self_iff_true,
      forall_const], },
  obtain ⟨v, hv, gh⟩ := module.End.has_eigenvector_iff_has_eigenvalue.mpr
    (@linear_map.is_symmetric.has_eigenvalue_eigenvalues 𝕜 _ _ E _ _ T
      hT.1 _ n hn i),
  have ugh := (linear_map.invertible_iff_inner_map_self_pos T hn hT).mp fs v gh,
  rw [hv, inner_smul_real_left, is_R_or_C.smul_re, inner_self_eq_norm_sq, mul_pos_iff] at ugh,
  simp_rw [not_lt_of_le (sq_nonneg _), and_false, or_false] at ugh,
  exact ugh.1,
end

noncomputable def is_positive.re_pow_is_invertible
  [decidable_eq 𝕜] (hT : T.is_positive) [invertible T] (r : ℝ) :
  invertible (T.re_pow hn hT.1 r) :=
begin
  apply invertible.mk (T.re_pow hn hT.1 (-r));
  ext1;
  simp_rw [linear_map.mul_apply, linear_map.re_pow_apply, inner_sum,
    inner_smul_right, orthonormal_iff_ite.mp (hT.1.eigenvector_basis hn).orthonormal,
    mul_boole, mul_ite, mul_zero, finset.sum_ite_eq, finset.mem_univ, if_true,
    smul_smul, ← mul_assoc, ← is_R_or_C.of_real_mul, ← real.rpow_add
      (linear_map.is_positive_and_invertible_pos_eigenvalues _ hn hT _), linear_map.one_apply];
  simp only [add_neg_self, neg_add_self, real.rpow_zero, is_R_or_C.of_real_one, one_mul,
    ← orthonormal_basis.repr_apply_apply, orthonormal_basis.sum_repr],
end


lemma is_positive.sum {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  {n : ℕ} {T : (fin n) → (E →ₗ[𝕜] E)} (hT : ∀ i, (T i).is_positive) :
  (∑ i, T i).is_positive :=
begin
  induction n with d hd,
  { simp only [finset.univ_eq_empty, finset.sum_empty, linear_map.is_positive_zero], },
  { simp_rw [fin.sum_univ_cast_succ],
    apply linear_map.is_positive.add,
    apply hd,
    { intros i,
      exact hT _, },
    { exact hT _, }, },
end

lemma is_positive.smul_nonneg {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  {T : E →ₗ[𝕜] E} (hT : T.is_positive) {r : ℝ} (hr : 0 ≤ r) :
  ((r : 𝕜) • T).is_positive :=
begin
  simp_rw [linear_map.is_positive, linear_map.is_symmetric, linear_map.smul_apply,
    inner_smul_left, inner_smul_right, is_R_or_C.conj_of_real, is_R_or_C.of_real_mul_re,
    hT.1 _ _, eq_self_iff_true, forall_2_true_iff, true_and, mul_nonneg hr (hT.2 _),
    forall_true_iff],
end

end finite_dimensional

end linear_map


namespace continuous_linear_map

open continuous_linear_map

variables [complete_space E] [complete_space F]

lemma is_positive.to_linear_map (T : E →L[𝕜] E) :
  T.to_linear_map.is_positive ↔ T.is_positive :=
by simp_rw [to_linear_map_eq_coe, linear_map.is_positive, continuous_linear_map.coe_coe,
            is_positive, is_self_adjoint_iff_is_symmetric, re_apply_inner_self_apply T,
            inner_re_symm]

end continuous_linear_map

lemma rank_one.is_positive {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E] (x : E) :
  (@rank_one 𝕜 E _ _ _ x x).is_positive :=
begin
  refine ⟨rank_one.is_self_adjoint _, _⟩,
  intros y,
  rw [continuous_linear_map.re_apply_inner_self_apply, rank_one_apply,
    inner_smul_left, is_R_or_C.conj_mul, is_R_or_C.of_real_re],
  exact is_R_or_C.norm_sq_nonneg _,
end

lemma linear_map.is_positive.nonneg_eigenvalue {E : Type*} [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.is_positive) {α : ℝ}
  (hα : module.End.has_eigenvalue T α) :
  0 ≤ α :=
begin
  have := (linear_map.is_positive.nonneg_spectrum T hT α
    (module.End.mem_spectrum_of_has_eigenvalue hα)).1,
  rw [map_zero, of_real_re] at this,
  exact this,
end

open_locale big_operators
lemma linear_map.is_positive_iff_eq_sum_rank_one {n : ℕ} [inner_product_space 𝕜 E]
  [decidable_eq 𝕜] [finite_dimensional 𝕜 E] (hn : finite_dimensional.finrank 𝕜 E = n)
  (T : E →ₗ[𝕜] E) :
  T.is_positive ↔ ∃ (m : ℕ) (u : fin m → E),
    T = ∑ i : fin m, ((rank_one (u i) (u i) : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
begin
  split,
  { intros hT,
    let a : fin n → E :=
    λ i, (real.sqrt (hT.1.eigenvalues hn i) : 𝕜) • (hT.1.eigenvector_basis hn i),
    refine ⟨n, a, _⟩,
    intros,
    ext1,
    simp_rw [linear_map.sum_apply, continuous_linear_map.coe_coe, rank_one_apply, a,
      inner_smul_left, smul_smul, mul_assoc, mul_rotate', is_R_or_C.conj_of_real,
      ← mul_assoc, ← is_R_or_C.of_real_mul, ← real.sqrt_mul
        (hT.nonneg_eigenvalue (hT.1.has_eigenvalue_eigenvalues hn _)),
      real.sqrt_mul_self (hT.nonneg_eigenvalue (hT.1.has_eigenvalue_eigenvalues hn _)),
      mul_comm _ (inner _ _), ← smul_eq_mul, smul_assoc, ← hT.1.apply_eigenvector_basis,
      ← linear_map.map_smul, ← map_sum, ← orthonormal_basis.repr_apply_apply,
      orthonormal_basis.sum_repr], },
  { rintros ⟨m, u, hu⟩,
    simp_rw [linear_map.is_positive, linear_map.is_symmetric, hu, linear_map.sum_apply,
      continuous_linear_map.coe_coe, rank_one_apply, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right, inner_conj_symm, mul_comm, eq_self_iff_true, forall_2_true_iff,
      true_and, map_sum],
    intros,
    apply finset.sum_nonneg',
    intros,
    simp_rw [← inner_conj_symm _ (u _), is_R_or_C.conj_mul, is_R_or_C.of_real_re,
      is_R_or_C.norm_sq_nonneg], },
end

lemma linear_map.is_symmetric.re_pow_is_positive_of_is_positive {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  [decidable_eq 𝕜] {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)
  {T : E →ₗ[𝕜] E} (hT : T.is_positive) (r : ℝ) :
  (T.re_pow hn hT.1 r).is_positive :=
begin
  haveI := finite_dimensional.complete 𝕜 E,
  simp_rw [linear_map.is_symmetric.re_pow_eq_rank_one],
  apply linear_map.is_positive.sum,
  intros i,
  apply linear_map.is_positive.smul_nonneg,
  { rw [← continuous_linear_map.to_linear_map_eq_coe,
      continuous_linear_map.is_positive.to_linear_map],
    exact rank_one.is_positive _, },
  { apply real.rpow_nonneg_of_nonneg,
    exact hT.nonneg_eigenvalue (hT.1.has_eigenvalue_eigenvalues hn _), },
end
