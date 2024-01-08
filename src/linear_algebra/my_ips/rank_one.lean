/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.adjoint
import linear_algebra.my_ips.basic
import linear_algebra.is_proj'

/-!

# rank one operators

This defines the rank one operator $| x \rangle\!\langle y |$ for continuous linear maps
  (see `rank_one`) and linear maps (see `rank_one_lm`).

-/

section rank_one
variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
local notation `L(`x`)` := x →L[ℂ] x

local notation `⟪` x `,` y `⟫_𝕜` := @inner 𝕜 _ _ x y

/-- we define the rank one operator $| x \rangle\!\langle y |$ by
  $x \mapsto \langle y,  z \rangle \cdot  x$ -/
def rank_one (x y : E) :
  E →L[𝕜] E :=
{ to_fun := λ z, ⟪y, z⟫_𝕜 • x,
  map_add' := λ u v, by { simp_rw [inner_add_right, add_smul], },
  map_smul' := λ r u, by { simp_rw [inner_smul_right, ring_hom.id_apply, smul_smul], } }

local notation `|` x `⟩⟨` y `|` := rank_one x y

@[simp] lemma rank_one_apply {x y : E} (z : E) :
  (|x⟩⟨y| : E →L[𝕜] E) z = ⟪y, z⟫_𝕜 • x :=
rfl

open continuous_linear_map

/-- $| x \rangle\!\langle \alpha\cdot y | = \bar{\alpha} \cdot | x \rangle\!\langle y |$ -/
@[simp] lemma rank_one.smul_apply {x y : E} {α : 𝕜} :
  |x⟩⟨α • y| = (star_ring_end 𝕜) α • (|x⟩⟨y| : E →L[𝕜] E) :=
begin
  ext,
  simp_rw [smul_apply, rank_one_apply, inner_smul_left, smul_smul],
end

/-- $| \alpha \cdot x \rangle\!\langle y | = \alpha \cdot | x \rangle\!\langle y |$ -/
@[simp] lemma rank_one.apply_smul {x y : E} {α : 𝕜} :
  |α • x⟩⟨y| = α • (|x⟩⟨y| : E →L[𝕜] E) :=
begin
  ext,
  simp_rw [smul_apply, rank_one_apply, smul_smul, mul_comm],
end

@[simp] lemma rank_one.smul_real_apply {x y : E} {α : ℝ} :
  |x⟩⟨(α : 𝕜) • y| = (α : 𝕜) • (|x⟩⟨y| : E →L[𝕜] E) :=
begin
  simp_rw [rank_one.smul_apply, is_R_or_C.conj_of_real],
end

/-- $| x \rangle\!\langle y | | z \rangle\!\langle w | = \langle y, z \rangle \cdot  | x \rangle\!\langle w |$ -/
@[simp] lemma rank_one.apply_rank_one (x y z w : E) :
  (|x⟩⟨y| : E →L[𝕜] E) ∘L (|z⟩⟨w| : _) = ⟪y, z⟫_𝕜 • (|x⟩⟨w| : _) :=
begin
  ext r,
  simp_rw [smul_apply, comp_apply, rank_one_apply, inner_smul_right, mul_comm, smul_smul],
end

/-- $u \circ | x \rangle\!\langle y | = | u(x) \rangle\!\langle y |$ -/
lemma continuous_linear_map.comp_rank_one
  (x y : E) (u : E →L[𝕜] E) :
  u ∘L |x⟩⟨y| = |u x⟩⟨y| :=
begin
  ext r,
  simp_rw [comp_apply, rank_one_apply, map_smul],
end

/-- $| x \rangle\!\langle y | \circ u  = | x \rangle\!\langle u^*(y) |$ -/
lemma continuous_linear_map.rank_one_comp [complete_space E] (x y : E) (u : E →L[𝕜] E) :
  |x⟩⟨y| ∘L (u : E →L[𝕜] E) = |x⟩⟨u.adjoint y| :=
begin
  ext r,
  simp_rw [comp_apply, rank_one_apply, adjoint_inner_left],
end

/-- rank one operators given by norm one vectors are automatically idempotent -/
@[simp] lemma rank_one.is_idempotent_elem (x : E) (h : ‖x‖ = 1) :
  is_idempotent_elem (|x⟩⟨x| : E →L[𝕜] E) :=
begin
  simp_rw [is_idempotent_elem, continuous_linear_map.ext_iff, mul_def,
    rank_one.apply_rank_one, inner_self_eq_norm_sq_to_K, h,
    is_R_or_C.of_real_one, one_pow, one_smul, eq_self_iff_true, forall_const],
end

lemma rank_one.is_symmetric (x : E) :
  linear_map.is_symmetric ((|x⟩⟨x| : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
begin
  simp_rw [linear_map.is_symmetric, continuous_linear_map.coe_coe, rank_one_apply,
    inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm, eq_self_iff_true,
    forall_2_true_iff],
end

/-- rank one operators are automatically self-adjoint -/
@[simp] lemma rank_one.is_self_adjoint [complete_space E] (x : E) :
  is_self_adjoint (|x⟩⟨x| : E →L[𝕜] E) :=
is_self_adjoint_iff_is_symmetric.mpr (rank_one.is_symmetric x)

/-- $| x \rangle\!\langle y |^* = | y \rangle\!\langle x |$ -/
lemma rank_one.adjoint [inner_product_space 𝕜 E] [complete_space E] (x y : E) :
  (|x⟩⟨y|).adjoint = (|y⟩⟨x| : E →L[𝕜] E) :=
begin
  ext a,
  apply @ext_inner_right 𝕜,
  intro b,
  simp_rw [adjoint_inner_left, rank_one_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm, mul_comm],
end

lemma rank_one_inner_left (x y z w : E) :
  ⟪(|x⟩⟨y| : E →L[𝕜] E) z, w⟫_𝕜 = ⟪z, y⟫_𝕜 * ⟪x, w⟫_𝕜 :=
begin
  rw [rank_one_apply, inner_smul_left, inner_conj_symm],
end

lemma rank_one_inner_right (x y z w : E) :
  ⟪x, (|y⟩⟨z| : E →L[𝕜] E) w⟫_𝕜 = ⟪z, w⟫_𝕜 * ⟪x, y⟫_𝕜 :=
begin
  rw [rank_one_apply, inner_smul_right],
end

lemma continuous_linear_map.commutes_with_all_iff [complete_space E] (T : E →L[𝕜] E) :
  (∀ S : E →L[𝕜] E, commute S T)
  ↔ ∃ α : 𝕜, T = α • 1 :=
begin
  split,
  { intros h,
    have h' : ∀ x y : E, |x⟩⟨y| ∘L T = T ∘L |x⟩⟨y| := λ x y, h _,
    simp_rw [continuous_linear_map.rank_one_comp, continuous_linear_map.comp_rank_one] at h',
    have h'' : ∀ x y : E, (|T.adjoint y⟩⟨x| : E →L[𝕜] E) = |y⟩⟨T x|,
    { intros x y,
      nth_rewrite_lhs 0 ← rank_one.adjoint,
      rw [h', rank_one.adjoint], },
    simp_rw [ext_iff, rank_one_apply] at h' h'',
    by_cases H : ∀ x : E, x = 0,
    { use 0,
      simp_rw [ext_iff],
      intros x,
      rw [H x, zero_smul, map_zero, zero_apply], },
    push_neg at H,
    obtain ⟨x, hx⟩ := H,
    use ((⟪x, x⟫_𝕜)⁻¹ * (⟪T.adjoint x, x⟫_𝕜)),
    simp_rw [ext_iff, smul_apply, one_apply, mul_smul, h', smul_smul],
    rw inv_mul_cancel,
    simp_rw [one_smul, eq_self_iff_true, forall_true_iff],
    { rw inner_self_ne_zero,
      exact hx, }, },
  { rintros ⟨α, hα⟩ S,
    simp_rw [commute, semiconj_by, mul_def, hα, comp_smul, smul_comp, one_def,
      comp_id, id_comp], },
end

lemma continuous_linear_map.centralizer [complete_space E] :
  (@set.univ (E →L[𝕜] E)).centralizer = {x : E →L[𝕜] E | ∃ α : 𝕜, x = α • 1} :=
begin
  simp_rw [set.centralizer, set.mem_univ, true_implies_iff,
    ← continuous_linear_map.commutes_with_all_iff],
  refl,
end

lemma continuous_linear_map.scalar_centralizer :
  {x : E →L[𝕜] E | ∃ α : 𝕜, x = α • 1}.centralizer = @set.univ (E →L[𝕜] E) :=
begin
  simp_rw [set.centralizer, set.ext_iff, set.mem_set_of, set.mem_univ, iff_true],
  rintros x y ⟨α, rfl⟩,
  simp_rw [smul_mul_assoc, one_mul, mul_smul_one],
end

lemma continuous_linear_map.centralizer_centralizer [complete_space E] :
  (@set.univ (E →L[𝕜] E)).centralizer.centralizer = set.univ :=
by rw [continuous_linear_map.centralizer, continuous_linear_map.scalar_centralizer]

lemma rank_one.zero_left {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x : E) :
  (rank_one 0 x : E →L[𝕜] E) = 0 :=
begin
  ext1,
  simp_rw [rank_one_apply, smul_zero, continuous_linear_map.zero_apply],
end

lemma rank_one.zero_right {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x : E) :
  (rank_one x 0 : E →L[𝕜] E) = 0 :=
begin
  ext1,
  simp_rw [rank_one_apply, inner_zero_left, zero_smul, continuous_linear_map.zero_apply],
end

lemma rank_one.ext_iff {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y : E) (h : (rank_one x x : E →L[𝕜] E) = rank_one y y) :
    ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
begin
  have : x = 0 ↔ y = 0,
  { split; intros hh;
    simp only [hh, continuous_linear_map.ext_iff, rank_one.zero_left,
      continuous_linear_map.zero_apply, @eq_comm _ (0 : E →L[𝕜] E), rank_one_apply,
      smul_eq_zero] at h,
    work_on_goal 1 { specialize h y, },
    work_on_goal 2 { specialize h x, },
    all_goals { simp_rw [inner_self_eq_zero, or_self] at h,
      exact h, }, },
  simp_rw [continuous_linear_map.ext_iff, rank_one_apply] at h,
  by_cases Hx : x = 0,
  { use 1,
    simp_rw [Hx, units.coe_one, one_smul, eq_comm, ← this, Hx], },
  { have ugh : inner y x ≠ (0 : 𝕜),
    { intros hy,
      specialize h x,
      rw [hy, zero_smul, smul_eq_zero, inner_self_eq_zero, or_self] at h,
      contradiction, },
    use units.mk0 ((inner y x) / (inner x x)) (div_ne_zero ugh
      ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx)),
    simp_rw [div_eq_inv_mul, units.coe_mk0, mul_action.mul_smul, ← h, smul_smul,
      inv_mul_cancel ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx), one_smul], },
end

lemma continuous_linear_map.ext_inner_map {F : Type*} [normed_add_comm_group F]
  [inner_product_space 𝕜 F] (T S : E →L[𝕜] F) :
  T = S ↔ ∀ x y, ⟪T x, y⟫_𝕜 = ⟪S x, y⟫_𝕜 :=
begin
  simp only [continuous_linear_map.ext_iff],
  split,
  { intros h x y,
    rw h, },
  { intros h x,
    apply @ext_inner_right 𝕜,
    exact h x, },
end

open_locale big_operators
lemma continuous_linear_map.exists_sum_rank_one [finite_dimensional 𝕜 E]
  (T : E →L[𝕜] E) :
  ∃ x y : fin (finite_dimensional.finrank 𝕜 E) × fin (finite_dimensional.finrank 𝕜 E) → E,
    T = ∑ i, |x i⟩⟨y i| :=
begin
  letI := finite_dimensional.complete 𝕜 E,
  let e := std_orthonormal_basis 𝕜 E,
  let a : fin (finite_dimensional.finrank 𝕜 E) × fin (finite_dimensional.finrank 𝕜 E) → E :=
  λ ij, (e.repr (T (e ij.1)) ij.2) • (e ij.2),
  let b : (fin (finite_dimensional.finrank 𝕜 E) × fin (finite_dimensional.finrank 𝕜 E)) → E
    := λ ij, e ij.1,
  refine ⟨a, b, _⟩,
  simp only [a, b],
  simp only [continuous_linear_map.ext_inner_map, sum_apply, sum_inner, rank_one_inner_left,
    inner_smul_left, orthonormal_basis.repr_apply_apply, inner_conj_symm],
  intros u v,
  symmetry,
  calc ∑ x : fin (finite_dimensional.finrank 𝕜 E) × fin (finite_dimensional.finrank 𝕜 E),
    ⟪u, e x.fst⟫_𝕜 * (⟪T (e x.fst), e x.snd⟫_𝕜 * ⟪e x.snd, v⟫_𝕜)
    = ∑ x_1 x_2 : fin (finite_dimensional.finrank 𝕜 E),
      ⟪u, e x_1⟫_𝕜 * (⟪T (e x_1), e x_2⟫_𝕜 * ⟪e x_2, v⟫_𝕜) :
  by { simp_rw [← finset.sum_product', finset.univ_product_univ], }
  ... = ∑ x_1, ⟪u, e x_1⟫_𝕜 * ⟪T (e x_1), v⟫_𝕜 :
  by { simp_rw [← finset.mul_sum, orthonormal_basis.sum_inner_mul_inner], }
  ... = ⟪T u, v⟫_𝕜 :
  by { simp_rw [← adjoint_inner_right T, orthonormal_basis.sum_inner_mul_inner], },
end

lemma linear_map.exists_sum_rank_one [finite_dimensional 𝕜 E]
  (T : E →ₗ[𝕜] E) :
  ∃ x y : fin (finite_dimensional.finrank 𝕜 E) × fin (finite_dimensional.finrank 𝕜 E) → E,
    T = ∑ i, ↑(|x i⟩⟨y i| : E →L[𝕜] E) :=
begin
  obtain ⟨a,b,h⟩ := continuous_linear_map.exists_sum_rank_one T.to_continuous_linear_map,
  refine ⟨a, b, _⟩,
  simp_rw [← coe_sum, ← h],
  refl,
end

lemma rank_one.sum_orthonormal_basis_eq_id {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] {ι : Type*} [fintype ι]
  (b : orthonormal_basis ι 𝕜 E) :
  ∑ i, (rank_one (b i) (b i) : E →L[𝕜] E) = 1 :=
begin
  rw [continuous_linear_map.ext_iff],
  intros,
  apply @ext_inner_left 𝕜 _,
  intros v,
  simp_rw [continuous_linear_map.sum_apply, rank_one_apply, ← orthonormal_basis.repr_apply_apply,
    orthonormal_basis.sum_repr, continuous_linear_map.one_apply],
end

end rank_one

section rank_one_lm

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]

local notation `⟪` x `,` y `⟫_𝕜` := @inner 𝕜 _ _ x y

/-- same as `rank_one`, but as a linear map -/
def rank_one_lm (x y : E) : E →ₗ[𝕜] E :=
(rank_one x y).to_linear_map

@[simp] lemma rank_one_lm_apply (x y z : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E) z = ⟪y, z⟫_𝕜 • x  :=
rfl

lemma rank_one_lm_comp_rank_one_lm (x y z w : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E) ∘ₗ (rank_one_lm z w) = ⟪y, z⟫_𝕜 • (rank_one_lm x w : _) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, rank_one_lm_apply,
    linear_map.smul_apply, inner_smul_right, mul_smul, rank_one_lm_apply,
    smul_smul, mul_comm, eq_self_iff_true, forall_true_iff],
end

lemma rank_one_lm_apply_rank_one (x y z w v : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E) ((rank_one_lm z w : E →ₗ[𝕜] E) v) = (⟪y, z⟫_𝕜 * ⟪w, v⟫_𝕜) • x :=
begin
  rw [← linear_map.comp_apply, rank_one_lm_comp_rank_one_lm, linear_map.smul_apply,
    rank_one_lm_apply, smul_smul],
end

lemma rank_one_lm_adjoint [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  (x y : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E).adjoint = rank_one_lm y x :=
begin
  simp_rw [rank_one_lm, linear_map.adjoint_eq_to_clm_adjoint,
    continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_inj,
    ← @rank_one.adjoint 𝕜 _ _ _ _ _ (finite_dimensional.complete 𝕜 E) x y],
  refl,
end

open_locale big_operators
lemma sum_rank_one [inner_product_space 𝕜 E] {n : Type*} [fintype n]
  (x : n → E) (y : E) :
  (rank_one (∑ i, x i) y : E →L[𝕜] E) = ∑ i, rank_one (x i) y :=
begin
  ext1 z,
  simp_rw [continuous_linear_map.sum_apply, rank_one_apply, finset.smul_sum],
end
lemma rank_one_sum [inner_product_space 𝕜 E] {n : Type*} [fintype n]
  (x : E) (y : n → E) :
  (rank_one x (∑ i, y i) : E →L[𝕜] E) = ∑ i, rank_one x (y i) :=
begin
  ext1 z,
  simp_rw [continuous_linear_map.sum_apply, rank_one_apply, sum_inner, finset.sum_smul],
end

lemma sum_rank_one_lm [inner_product_space 𝕜 E] {n : Type*} [fintype n]
  (x : n → E) (y : E) :
  (rank_one_lm (∑ i : n, x i) y : E →ₗ[𝕜] E) = ∑ i : n, rank_one_lm (x i) y :=
begin
  rw [rank_one_lm, sum_rank_one, continuous_linear_map.to_linear_map_eq_coe,
    continuous_linear_map.coe_sum],
  refl,
end

lemma rank_one_lm_sum [inner_product_space 𝕜 E] {n : Type*} [fintype n] (x : E) (y : n → E) :
  (rank_one_lm x (∑ i : n, y i) : E →ₗ[𝕜] E) = ∑ i : n, rank_one_lm x (y i) :=
begin
  rw [rank_one_lm, rank_one_sum, continuous_linear_map.to_linear_map_eq_coe,
    continuous_linear_map.coe_sum],
  refl,
end

end rank_one_lm


lemma linear_map.ext_of_rank_one {𝕜 H H' : Type*} [is_R_or_C 𝕜]
  [add_comm_monoid H'] [module 𝕜 H']
  [normed_add_comm_group H] [inner_product_space 𝕜 H] [finite_dimensional 𝕜 H]
  {x y : (H →L[𝕜] H) →ₗ[𝕜] H'}
  (h : ∀ a b : H, x (rank_one a b) = y (rank_one a b)) :
  x = y :=
begin
  ext a,
  obtain ⟨α, β, rfl⟩ := continuous_linear_map.exists_sum_rank_one a,
  simp_rw [map_sum, h],
end
lemma linear_map.ext_of_rank_one' {𝕜 H H' : Type*} [is_R_or_C 𝕜]
  [add_comm_monoid H'] [module 𝕜 H']
  [normed_add_comm_group H] [inner_product_space 𝕜 H] [finite_dimensional 𝕜 H]
  {x y : (H →ₗ[𝕜] H) →ₗ[𝕜] H'}
  (h : ∀ a b : H, x ↑(@rank_one 𝕜 _ _ _ _ a b) = y ↑(@rank_one 𝕜 _ _ _ _ a b)) :
  x = y :=
begin
  ext a,
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one a,
  simp_rw [map_sum, h],
end

open_locale big_operators
lemma rank_one.sum_orthonormal_basis_eq_id_lm {𝕜 : Type*} {E : Type*}
  [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  {ι : Type*}  [fintype ι] (b : orthonormal_basis ι 𝕜 E) :
  ∑ i, ((@rank_one 𝕜 E _ _ _ (b i) (b i)) : E →ₗ[𝕜] E) = 1 :=
begin
  simp only [← continuous_linear_map.coe_sum, rank_one.sum_orthonormal_basis_eq_id b],
  refl,
end


lemma continuous_linear_map.coe_eq_zero {𝕜 E₁ E₂ : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E₁]
  [normed_add_comm_group E₂] [inner_product_space 𝕜 E₁] [inner_product_space 𝕜 E₂]
  (f : E₁ →L[𝕜] E₂) :
  (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 :=
begin
  norm_cast,
end

lemma rank_one.eq_zero_iff {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y : E) :
  (rank_one x y : E →L[𝕜] E) = 0 ↔ x = 0 ∨ y = 0 :=
begin
  simp_rw [continuous_linear_map.ext_iff, rank_one_apply, continuous_linear_map.zero_apply,
    smul_eq_zero, forall_or_distrib_right, forall_inner_eq_zero_iff, or_comm],
end

lemma rank_one.left_add {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y z : E) :
  (rank_one (x + y) z : E →L[𝕜] E) = rank_one x z + rank_one y z :=
begin
  ext,
  simp only [rank_one_apply, continuous_linear_map.add_apply, smul_add],
end
lemma rank_one.right_add {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y z : E) :
  (rank_one x (y + z) : E →L[𝕜] E) = rank_one x y + rank_one x z :=
begin
  ext,
  simp only [rank_one_apply, continuous_linear_map.add_apply, inner_add_left, add_smul],
end
lemma rank_one.left_sub {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y z : E) :
  (rank_one (x - y) z : E →L[𝕜] E) = rank_one x z - rank_one y z :=
begin
  ext,
  simp only [rank_one_apply, continuous_linear_map.sub_apply, smul_sub],
end
lemma rank_one.right_sub {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y z : E) :
  (rank_one x (y - z) : E →L[𝕜] E) = rank_one x y - rank_one x z :=
begin
  ext,
  simp only [rank_one_apply, continuous_linear_map.sub_apply, inner_sub_left, sub_smul],
end

lemma linear_map.rank_one_comp {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
  ((rank_one x y : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ u = (rank_one x (u.adjoint y) : E →L[𝕜] E) :=
begin
  ext,
  simp_rw [linear_map.comp_apply, continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.adjoint_inner_left],
end
lemma linear_map.rank_one_comp' {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
  ((rank_one x y : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ u.adjoint = (rank_one x (u y) : E →L[𝕜] E) :=
begin
  rw [linear_map.rank_one_comp, linear_map.adjoint_adjoint],
end


lemma orthonormal_basis.orthogonal_projection'_eq_sum_rank_one {ι 𝕜 : Type*}
  [is_R_or_C 𝕜] {E : Type*} [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [fintype ι] {U : submodule 𝕜 E} [complete_space ↥U] (b : orthonormal_basis ι 𝕜 ↥U) :
  orthogonal_projection' U = ∑ (i : ι), rank_one (b i : E) (b i : E) :=
begin
  ext,
  simp_rw [orthogonal_projection'_apply, b.orthogonal_projection_eq_sum,
    continuous_linear_map.sum_apply, rank_one_apply, submodule.coe_sum,
    submodule.coe_smul_of_tower],
end



lemma linear_map.comp_rank_one {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [inner_product_space 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
  u ∘ₗ ((rank_one x y : E →L[𝕜] E) : E →ₗ[𝕜] E) = (rank_one (u x) y : E →L[𝕜] E) :=
begin
  ext,
  simp_rw [linear_map.comp_apply, continuous_linear_map.coe_coe, rank_one_apply,
    smul_hom_class.map_smul],
end