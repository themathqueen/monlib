/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.functional
import linear_algebra.my_matrix.pos_def_rpow
import linear_algebra.mul''
import linear_algebra.my_ips.basic
import linear_algebra.pi_direct_sum

/-!

# The inner product space on finite dimensional C*-algebras

This file contains some basic results on the inner product space on finite dimensional C*-algebras.

-/

open_locale tensor_product functional

/-- A lemma that states the right multiplication property of a linear functional. -/
lemma linear_functional_right_mul {R A : Type*} [comm_semiring R] [semiring A]
  [algebra R A] [star_semigroup A] {φ : A →ₗ[R] R}
  (x y z : A) :
  φ (star (x * y) * z) = φ (star y * (star x * z)) :=
by rw [star_semigroup.star_mul, mul_assoc]

/-- A lemma that states the left multiplication property of a linear functional. -/
lemma linear_functional_left_mul {R A : Type*} [comm_semiring R] [semiring A]
  [algebra R A] [star_semigroup A] {φ : A →ₗ[R] R}
  (x y z : A) :
  φ (star x * (y * z)) = φ (star (star y * x) * z) :=
by rw [star_semigroup.star_mul, star_star, mul_assoc]

variables {k : Type*} [fintype k] [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)]
  [Π i, decidable_eq (s i)] {ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]

open matrix

open_locale matrix big_operators

/-- A function that returns the direct sum of matrices for each index of type 'i'. -/
def linear_map.direct_sum_matrix_block (ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ) :
  Π i, matrix (s i) (s i) ℂ :=
∑ i, (ψ i).matrix.include_block

/-- A function that returns a direct sum matrix. -/
def linear_map.direct_sum_matrix (ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ) :
  matrix (Σ i, s i) (Σ i, s i) ℂ :=
block_diagonal' (linear_map.direct_sum_matrix_block ψ)

/-- A lemma that states the inner product of two direct sum matrices is the sum of the inner products of their components. -/
lemma inner_direct_sum_eq_sum [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y : Π i, matrix (s i) (s i) ℂ) :
  ⟪x, y⟫_ℂ = ∑ i, ⟪x i, y i⟫_ℂ :=
rfl

lemma linear_map.direct_sum_matrix_block_apply {i : k} :
  linear_map.direct_sum_matrix_block ψ i = (ψ i).matrix :=
begin
  simp only [linear_map.direct_sum_matrix_block, finset.sum_apply, include_block,
    linear_map.coe_mk, finset.sum_dite_eq', finset.mem_univ, if_true],
  refl,
end

/-- A function that returns a star algebra equivalence for each index of type 'i'. -/
def star_alg_equiv.direct_sum {𝕜 : Type*} [is_R_or_C 𝕜]
  {k : Type u_1}  [fintype k]  [decidable_eq k] {s : k → Type*}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  (f : Π i, matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] matrix (s i) (s i) 𝕜) :
  (Π i, matrix (s i) (s i) 𝕜) ≃⋆ₐ[𝕜] Π i, matrix (s i) (s i) 𝕜 :=
{ to_fun := λ x i, f i (x i),
  inv_fun := λ x i, (f i).symm (x i),
  left_inv := λ a, by {
    simp only [star_alg_equiv.symm_apply_apply], },
  right_inv := λ a, by {
    simp only [star_alg_equiv.apply_symm_apply], },
  map_add' := λ a y, by {
    simp only [pi.add_apply, map_add],
    refl, },
  map_smul' := λ r a, by {
    simp only [pi.smul_apply, smul_hom_class.map_smul],
    refl, },
  map_mul' := λ a b, by {
    simp only [pi.mul_apply, _root_.map_mul],
    refl, },
  map_star' := λ a, by {
    simp only [pi.star_apply, map_star],
    refl, } }

lemma star_alg_equiv.direct_sum_apply {𝕜 : Type*} [is_R_or_C 𝕜]
  {k : Type u_1}  [fintype k]  [decidable_eq k] {s : k → Type*}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  (f : Π i, matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] matrix (s i) (s i) 𝕜)
  (x : Π i, matrix (s i) (s i) 𝕜) (i : k) :
  star_alg_equiv.direct_sum f x i = f i (x i) :=
rfl

/-- the unitary element from the star algebraic equivalence -/
noncomputable def star_alg_equiv.direct_sum.unitary {𝕜 : Type*} [is_R_or_C 𝕜]
  {k : Type u_1}  [fintype k]  [decidable_eq k] {s : k → Type*}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  (f : Π i, matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] matrix (s i) (s i) 𝕜) :
  Π i, unitary_group (s i) 𝕜 :=
λ i, (f i).unitary

lemma star_alg_equiv.direct_sum.unitary_apply {𝕜 : Type*} [is_R_or_C 𝕜]
  {k : Type u_1}  [fintype k]  [decidable_eq k] {s : k → Type*}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  (f : Π i, matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] matrix (s i) (s i) 𝕜) (a : k) :
  (star_alg_equiv.direct_sum.unitary f) a = (f a).unitary :=
rfl

/-- any $^*$-isomorphism on $\bigoplus_i M_{n_i}$ is an inner automorphism -/
lemma star_alg_equiv.of_direct_sum_matrix_is_inner {𝕜 : Type*} [is_R_or_C 𝕜]
  {k : Type u_1}  [fintype k]  [decidable_eq k] {s : k → Type*}
  [Π (i : k), fintype (s i)] [Π (i : k), decidable_eq (s i)]
  (f : Π i, matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] matrix (s i) (s i) 𝕜) :
  unitary.inner_aut_star_alg 𝕜
    (unitary.pi (star_alg_equiv.direct_sum.unitary f))
    = star_alg_equiv.direct_sum f :=
begin
  simp_rw [star_alg_equiv.ext_iff, unitary.inner_aut_star_alg_apply, function.funext_iff,
    pi.mul_apply, unitary.pi_apply, unitary.coe_star, pi.star_apply, unitary.pi_apply,
    star_alg_equiv.direct_sum_apply, star_alg_equiv.direct_sum.unitary_apply],
  intros,
  rw [← unitary.coe_star, ← @unitary.inner_aut_star_alg_apply 𝕜 _ _ _ _ _
    ((f a_1).unitary) (a a_1)],
  congr,
  exact star_alg_equiv.eq_inner_aut _,
end


def incl_pi {i : k} (x : s i → ℂ) :
  (Σ j, s j) → ℂ :=
λ j, dite (i = j.1) (λ h, x (by { rw h, exact j.2, })) (λ h, 0)
def excl_pi (x : (Σ j, s j) → ℂ) (i : k) :
  s i → ℂ :=
λ j, x ⟨i,j⟩

private lemma pi.forall_left_mul (x y : Π i, matrix (s i) (s i) ℂ) :
  (∀ a, a * x = a * y) ↔ x = y :=
begin
  split,
  { intros h,
    specialize h 1,
    simp_rw one_mul at h,
    exact h, },
  { rintros rfl a,
    refl, },
end

lemma linear_map.direct_sum.linear_functional_eq'' (ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ)
  (x : Π i, matrix (s i) (s i) ℂ) :
  linear_map.direct_sum ψ x
    = (block_diagonal' (linear_map.direct_sum_matrix_block ψ) * block_diagonal' x).trace :=
begin
  simp_rw [linear_map.direct_sum.linear_functional_eq', linear_map.direct_sum_matrix_block,
    ← block_diagonal'_alg_hom_apply, map_sum, finset.sum_mul, trace_sum, mul_eq_mul],
end

lemma star_alg_equiv.direct_sum_is_trace_preserving
  (f : Π i, matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] matrix (s i) (s i) ℂ) (x : Π i, matrix (s i) (s i) ℂ) :
  (block_diagonal'_alg_hom ((star_alg_equiv.direct_sum f) x)).trace
    = (block_diagonal'_alg_hom x).trace :=
begin
  rw matrix_eq_sum_include_block ((star_alg_equiv.direct_sum f) x),
  nth_rewrite_rhs 0 matrix_eq_sum_include_block x,
  simp only [map_sum, trace_sum],
  simp only [block_diagonal'_alg_hom_apply, block_diagonal'_include_block_trace,
    star_alg_equiv.direct_sum_apply, star_alg_equiv.trace_preserving],
end

lemma star_alg_equiv.direct_sum_symm_apply_apply
  (f : Π i, matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] matrix (s i) (s i) ℂ)
  (x : Π i, matrix (s i) (s i) ℂ) :
  (star_alg_equiv.direct_sum (λ i, (f i).symm))
    ((star_alg_equiv.direct_sum f) x) = x :=
begin
  ext1,
  simp only [star_alg_equiv.direct_sum_apply, star_alg_equiv.symm_apply_apply],
end

lemma linear_map.linear_functional_direct_sum_eq_of (ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ)
  (x : Π i, matrix (s i) (s i) ℂ)
  (h : ∀ a, linear_map.direct_sum ψ a = (block_diagonal' x * block_diagonal' a).trace) :
  x = linear_map.direct_sum_matrix_block ψ :=
begin
  ext1,
  simp only [linear_map.direct_sum_matrix_block_apply],
  apply linear_map.linear_functional_eq_of,
  intros a,
  let a' := include_block a,
  have ha' : a = a' x_1 := by simp only [a', include_block_apply_same],
  specialize h a',
  simp_rw [ha', ← linear_map.direct_sum_apply_single_block,
    ← mul_eq_mul, ← pi.mul_apply, ← block_diagonal'_include_block_trace,
    ← ha', pi.mul_apply, ← ha'],
  simp only [← block_diagonal'_alg_hom_apply, ← _root_.map_mul, a',
    mul_include_block] at h,
  exact h,
end

lemma star_alg_equiv.direct_sum_symm_apply_eq
  (f : Π i, matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] matrix (s i) (s i) ℂ)
  (x y : Π i, matrix (s i) (s i) ℂ) :
  star_alg_equiv.direct_sum (λ i, (f i).symm) x = y
    ↔ x = star_alg_equiv.direct_sum f y :=
begin
  split,
  { rintros rfl,
    ext1,
    simp only [star_alg_equiv.direct_sum_apply, star_alg_equiv.apply_symm_apply], },
  { rintros rfl,
    ext1,
    simp only [star_alg_equiv.direct_sum_apply, star_alg_equiv.symm_apply_apply], },
end

section single_block
/-!
  ## Section `single_block`
-/

variables {n : Type*} [decidable_eq n] [fintype n]
  {φ : matrix n n ℂ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map]

namespace linear_map.is_faithful_pos_map

lemma inner_eq [hφ : fact φ.is_faithful_pos_map]
  (x y : matrix n n ℂ) :
  ⟪x, y⟫_ℂ  = φ (xᴴ ⬝ y) :=
rfl

lemma inner_eq' [hφ : fact φ.is_faithful_pos_map]
  (x y : matrix n n ℂ) :
  ⟪x, y⟫_ℂ = (φ.matrix ⬝ xᴴ ⬝ y).trace :=
by rw [inner_eq, φ.linear_functional_eq', matrix.mul_assoc]

def matrix_is_pos_def (hφ : φ.is_faithful_pos_map) :
  φ.matrix.pos_def :=
φ.is_faithful_pos_map_iff_of_matrix.mp hφ

lemma linear_functional_mul_right (hφ : φ.is_faithful_pos_map)
  (x y z : matrix n n ℂ) :
  φ (xᴴ ⬝ (y ⬝ z)) = φ ((x ⬝ (φ.matrix ⬝ zᴴ ⬝ φ.matrix⁻¹))ᴴ ⬝ y) :=
begin
  haveI := hφ.matrix_is_pos_def.invertible,
  simp_rw [φ.linear_functional_eq', matrix.conj_transpose_mul,
    matrix.conj_transpose_conj_transpose, hφ.matrix_is_pos_def.1.eq, hφ.matrix_is_pos_def.inv.1.eq,
    ← matrix.mul_assoc, matrix.mul_assoc, matrix.mul_inv_cancel_left_of_invertible],
  rw [matrix.trace_mul_cycle', matrix.mul_assoc, ← matrix.trace_mul_cycle', matrix.mul_assoc],
end

lemma inner_left_mul [hφ : fact φ.is_faithful_pos_map]
  (x y z : matrix n n ℂ) :
  ⟪x ⬝ y, z⟫_ℂ = ⟪y, xᴴ ⬝ z⟫_ℂ :=
linear_functional_right_mul _ _ _

lemma inner_right_mul [hφ : fact φ.is_faithful_pos_map]
  (x y z : matrix n n ℂ) :
  ⟪x, y ⬝ z⟫_ℂ = ⟪yᴴ ⬝ x, z⟫_ℂ :=
linear_functional_left_mul _ _ _

lemma inner_left_conj [hφ : fact φ.is_faithful_pos_map]
  (x y z : matrix n n ℂ) :
  ⟪x, y ⬝ z⟫_ℂ = ⟪x ⬝ (φ.matrix ⬝ zᴴ ⬝ φ.matrix⁻¹), y⟫_ℂ :=
hφ.elim.linear_functional_mul_right _ _ _

lemma linear_functional_mul_left (hφ : φ.is_faithful_pos_map) (x y z : matrix n n ℂ) :
  φ ((x ⬝ y)ᴴ ⬝ z) = φ (xᴴ ⬝ (z ⬝ (φ.matrix ⬝ yᴴ ⬝ φ.matrix⁻¹))) :=
begin
  letI := fact.mk hφ,
  rw [← inner_eq, ← inner_product_space.core.inner_conj_symm, inner_left_conj,
    inner_product_space.core.inner_conj_symm],
  refl,
end

lemma inner_right_conj [hφ : fact φ.is_faithful_pos_map] (x y z : matrix n n ℂ) :
  ⟪x ⬝ y, z⟫_ℂ = ⟪x, z ⬝ (φ.matrix ⬝ yᴴ ⬝ φ.matrix⁻¹)⟫_ℂ :=
hφ.elim.linear_functional_mul_left _ _ _

lemma adjoint_eq [hφ : fact φ.is_faithful_pos_map] :
  φ.adjoint = (algebra.linear_map ℂ (matrix n n ℂ) : ℂ →ₗ[ℂ] matrix n n ℂ) :=
begin
  rw linear_map.ext_iff,
  intros x,
  apply @ext_inner_right ℂ,
  intros y,
  rw [linear_map.adjoint_inner_left, algebra.linear_map_apply,
    algebra.algebra_map_eq_smul_one, inner_product_space.core.inner_smul_left,
    inner_eq, conj_transpose_one, matrix.one_mul],
  refl,
end


/-- The adjoint of a star-algebraic equivalence $f$ on matrix algebras is given by
  $$f^*\colon x \mapsto f^{-1}(x Q) Q^{-1},$$
  where $Q$ is `hφ.matrix`. -/
lemma star_alg_equiv_adjoint_eq [hφ : fact φ.is_faithful_pos_map]
  (f : matrix n n ℂ ≃⋆ₐ[ℂ] matrix n n ℂ) (x : matrix n n ℂ) :
  ((f : matrix n n ℂ ≃⋆ₐ[ℂ] matrix n n ℂ).to_alg_equiv.to_linear_map : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ).adjoint x
    = (f.symm (x ⬝ φ.matrix) : matrix n n ℂ) ⬝ φ.matrix⁻¹ :=
begin
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  apply @ext_inner_left ℂ,
  intros a,
  simp_rw [linear_map.adjoint_inner_right, alg_equiv.to_linear_map_apply,
    star_alg_equiv.coe_to_alg_equiv],
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner,
  simp_rw [inner_aut_star_alg_apply, inner_aut_star_alg_symm_apply, matrix.mul_assoc],
  nth_rewrite_rhs 0 ← matrix.mul_assoc (φ.matrix),
  nth_rewrite_rhs 0 ← matrix.mul_assoc,
  rw [inner_left_conj, inner_right_mul],
  simp_rw [conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.eq, hφ.elim.matrix_is_pos_def.inv.1.eq,
    ← star_eq_conj_transpose, ← unitary_group.star_coe_eq_coe_star, star_star,
    matrix.mul_inv_cancel_left_of_invertible, matrix.mul_assoc,
    mul_inv_of_invertible, matrix.mul_one],
end

/-- Let $f$ be a  star-algebraic equivalence on matrix algebras. Then tfae:

  - $f(Q)=Q$ where $Q$ is `hφ.matrix`,
  - $f^* = f⁻¹$,
  - $\phi \circ f = \phi$,
  - $\langle f(x)|f(y) \rangle = \langle x | y \rangle$ for all $x,y \in M_n$,
  - $‖f x‖ = ‖x‖$ for all $x$. -/
lemma star_alg_equiv_is_isometry_tfae [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] (f : matrix n n ℂ ≃⋆ₐ[ℂ] matrix n n ℂ) :
  tfae [f φ.matrix = φ.matrix,
      ((f : matrix n n ℂ ≃⋆ₐ[ℂ] matrix n n ℂ).to_alg_equiv.to_linear_map : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ).adjoint = f.symm.to_alg_equiv.to_linear_map,
    φ ∘ₗ f.to_alg_equiv.to_linear_map = φ,
    ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ,
    ∀ x : matrix n n ℂ, ‖f x‖ = ‖x‖] :=
begin
  tfae_have : 5 ↔ 2,
  { simp_rw [inner_product_space.core.norm_eq_sqrt_inner,
    real.sqrt_inj inner_product_space.core.inner_self_nonneg
      inner_product_space.core.inner_self_nonneg, ← complex.of_real_inj,
    inner_self_re, ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ],
    have : ∀ x y, ⟪f x, f y⟫_ℂ - ⟪x, y⟫_ℂ
      = ⟪(f.to_alg_equiv.to_linear_map.adjoint ∘ₗ f.to_alg_equiv.to_linear_map - 1) x, y⟫_ℂ,
    { intros x y,
      simp only [linear_map.sub_apply, linear_map.one_apply, inner_sub_left,
        linear_map.comp_apply, linear_map.adjoint_inner_left, star_alg_equiv.coe_to_alg_equiv,
        alg_equiv.to_linear_map_apply], },
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, star_alg_equiv.comp_eq_iff,
      linear_map.one_comp], },
  rw tfae_5_iff_2,
  tfae_have : 4 ↔ 3,
  { simp_rw [inner_eq, ← star_eq_conj_transpose, ← map_star f, ← mul_eq_mul,
      ← _root_.map_mul f, linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv],
    refine ⟨λ h x, _, λ h x y, h _⟩,
    rw [← matrix.one_mul x, ← star_one, ← mul_eq_mul],
    exact h _ _, },
  rw tfae_4_iff_3,
  haveI := hφ.elim.matrix_is_pos_def.invertible,
  simp_rw [linear_map.ext_iff, star_alg_equiv_adjoint_eq f, linear_map.comp_apply,
    alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv,
    mul_inv_eq_iff_eq_mul_of_invertible, φ.linear_functional_eq',
    star_alg_equiv.symm_apply_eq, ← mul_eq_mul, _root_.map_mul, star_alg_equiv.apply_symm_apply,
    ← forall_left_mul φ.matrix, @eq_comm _ φ.matrix],
  tfae_have : 1 ↔ 2,
  { rw iff_self, trivial, },
  tfae_have : 1 → 3,
  { intros i x,
    nth_rewrite 0 ← i,
    rw [← _root_.map_mul, f.trace_preserving], },
  tfae_have : 3 → 1,
  { intros i,
    simp_rw [← f.symm.trace_preserving (φ.matrix * (f _)), _root_.map_mul,
      star_alg_equiv.symm_apply_apply, mul_eq_mul, ← φ.linear_functional_eq',
      @eq_comm _ _ (φ _)] at i,
    obtain ⟨Q, hQ, h⟩ := φ.linear_functional_eq,
    have := h _ i,
    rw star_alg_equiv.symm_apply_eq at this,
    nth_rewrite_rhs 0 this,
    congr',
    exact h _ φ.linear_functional_eq', },
  tfae_finish,
end

protected noncomputable def basis (hφ : φ.is_faithful_pos_map) :
  basis (n × n) ℂ (matrix n n ℂ) :=
begin
  let hQ := hφ.matrix_is_pos_def,
  refine basis.mk _ _,
  { exact λ ij, std_basis_matrix ij.1 ij.2 1 ⬝ hφ.matrix_is_pos_def.rpow (-(1/2)), },
  { have := (std_basis ℂ n n).linear_independent,
    simp_rw [linear_independent, linear_map.ker_eq_bot, injective_iff_map_eq_zero,
      finsupp.total_apply, finsupp.sum] at this ⊢,
    simp_rw [← mul_eq_mul, ← smul_mul_assoc, ← finset.sum_mul],
    by_cases is_empty n,
    { haveI := h,
      simp only [eq_iff_true_of_subsingleton, forall_const], },
    rw not_is_empty_iff at h,
    have t1 : ∀ (a : n × n →₀ ℂ), (∑ (x : n × n) in a.support,
      (a x) • (std_basis_matrix x.fst x.snd 1 : matrix n n ℂ))
        * hQ.rpow (-(1 / 2)) = 0
      ↔ (∑ (x : n × n) in a.support, a x • (std_basis_matrix x.fst x.snd 1 : matrix n n ℂ))
        * hQ.rpow (-(1 / 2)) * hQ.rpow (1 / 2)
      = 0 * hQ.rpow (1 / 2),
    { intros a,
      split; intros h,
      { rw h, },
      { simp_rw [mul_assoc, mul_eq_mul, matrix.pos_def.rpow_mul_rpow, neg_add_self,
          matrix.pos_def.rpow_zero, matrix.mul_one] at h,
        rw [h, matrix.zero_mul, zero_mul], }, },
    simp_rw [t1, mul_assoc, mul_eq_mul, matrix.pos_def.rpow_mul_rpow,
      neg_add_self, matrix.pos_def.rpow_zero, matrix.zero_mul, matrix.mul_one,
      ← std_basis_eq_std_basis_matrix ℂ, prod.mk.eta],
    exact this, },
  { simp_rw [top_le_iff],
    ext,
    simp_rw [submodule.mem_top, iff_true, mem_span_range_iff_exists_fun,
      ← smul_mul, ← mul_eq_mul, ← finset.sum_mul, ← matrix.ext_iff, mul_eq_mul,
      mul_apply, matrix.sum_apply, pi.smul_apply, std_basis_matrix, smul_ite, smul_zero,
      ← prod.mk.inj_iff, prod.mk.eta, finset.sum_ite_eq', finset.mem_univ, if_true,
      smul_mul_assoc, one_mul],
    existsi (λ ij : n × n, ((x ⬝ hQ.rpow (1/2)) : matrix n n ℂ) ij.1 ij.2),
    simp_rw [smul_eq_mul, ← mul_apply, matrix.mul_assoc, matrix.pos_def.rpow_mul_rpow,
      add_neg_self, matrix.pos_def.rpow_zero, matrix.mul_one, eq_self_iff_true,
      forall_2_true_iff], },
end

protected lemma basis_apply (hφ : φ.is_faithful_pos_map) (ij : n × n) :
  hφ.basis ij = std_basis_matrix ij.1 ij.2 (1 : ℂ) ⬝ hφ.matrix_is_pos_def.rpow (-(1/2 : ℝ)) :=
begin
  rw [is_faithful_pos_map.basis, basis.mk_apply],
end


local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y

protected noncomputable def to_matrix (hφ : φ.is_faithful_pos_map) :
  (matrix n n ℂ →ₗ[ℂ] matrix n n ℂ) ≃ₐ[ℂ] matrix (n × n) (n × n) ℂ :=
linear_map.to_matrix_alg_equiv hφ.basis

lemma basis_is_orthonormal [hφ : fact φ.is_faithful_pos_map] :
  orthonormal ℂ hφ.elim.basis :=
begin
  rw orthonormal_iff_ite,
  simp_rw [linear_map.is_faithful_pos_map.basis_apply],
  simp_rw [inner_eq', conj_transpose_mul, (pos_def.rpow.is_hermitian _ _).eq,
    std_basis_matrix.star_one, matrix.mul_assoc, ← matrix.mul_assoc _ (std_basis_matrix _ _ _),
    std_basis_matrix_mul, one_mul, matrix.smul_mul, matrix.mul_smul,
    trace_smul, smul_eq_mul, boole_mul],
  let Q := φ.matrix,
  let hQ := hφ.elim.matrix_is_pos_def,
  have : ∀ i j : n,
    (Q ⬝ (hQ.rpow (-(1 / 2) : ℝ) ⬝ (std_basis_matrix i j 1
      ⬝ hQ.rpow (-(1 / 2) : ℝ)))).trace = ite (i = j) (1 : ℂ) (0 : ℂ) := λ i j,
  calc (Q ⬝ (hQ.rpow (-(1 / 2) : ℝ) ⬝ (std_basis_matrix i j 1
      ⬝ hQ.rpow (-(1 / 2) : ℝ)))).trace
    = ((hQ.rpow (-(1/2) : ℝ) ⬝ hQ.rpow 1 ⬝ hQ.rpow (-(1/2) : ℝ))
      ⬝ std_basis_matrix i j 1).trace :
  by { simp_rw [pos_def.rpow_one_eq_self, matrix.mul_assoc],
    rw [← trace_mul_cycle', trace_mul_comm],
    simp_rw [matrix.mul_assoc],
    rw trace_mul_comm,
    simp_rw [matrix.mul_assoc], }
    ... = ((hQ.rpow (-(1/2) + 1 + -(1/2) : ℝ)) ⬝ std_basis_matrix i j 1).trace :
  by { simp_rw [pos_def.rpow_mul_rpow], }
    ... = (hQ.rpow 0 ⬝ std_basis_matrix i j 1).trace : by norm_num
    ... = ite (i = j) 1 0 : by { simp_rw [pos_def.rpow_zero, matrix.one_mul,
      std_basis_matrix.trace], },
  simp_rw [this, ← ite_and, ← prod.eq_iff_fst_eq_snd_eq, eq_self_iff_true, forall_2_true_iff],
end

protected noncomputable def orthonormal_basis
  [hφ : fact φ.is_faithful_pos_map] :
  orthonormal_basis (n × n) ℂ (matrix n n ℂ) :=
hφ.elim.basis.to_orthonormal_basis basis_is_orthonormal

protected lemma orthonormal_basis_apply [hφ : fact φ.is_faithful_pos_map]
  (ij : n × n) :
  (is_faithful_pos_map.orthonormal_basis : orthonormal_basis (n × n) ℂ (matrix n n ℂ)) ij
    = std_basis_matrix ij.1 ij.2 (1 : ℂ) ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1/2 : ℝ)) :=
begin
  rw [← is_faithful_pos_map.basis_apply, is_faithful_pos_map.orthonormal_basis,
    basis.coe_to_orthonormal_basis],
end

lemma inner_coord [hφ : fact φ.is_faithful_pos_map]
  (ij : n × n) (y : matrix n n ℂ) :
  ⟪(is_faithful_pos_map.orthonormal_basis : orthonormal_basis _ _ _) ij, y⟫_ℂ
    = (y ⬝ hφ.elim.matrix_is_pos_def.rpow (1 / 2)) ij.1 ij.2 :=
begin
  let Q := φ.matrix,
  let hQ := hφ.elim.matrix_is_pos_def,
  simp_rw [inner_eq', is_faithful_pos_map.orthonormal_basis_apply, conj_transpose_mul,
    (matrix.pos_def.rpow.is_hermitian hQ _).eq, ← matrix.mul_assoc,
    std_basis_matrix_conj_transpose, star_one],
  have := calc Q ⬝ hQ.rpow (-(1 / 2)) = hQ.rpow (1) ⬝ hQ.rpow (-(1 / 2)) :
  by rw [matrix.pos_def.rpow_one_eq_self]
    ... = hQ.rpow (1 + -(1 / 2)) : by rw [matrix.pos_def.rpow_mul_rpow]
    ... = hQ.rpow (1 / 2) : by norm_num,
  rw this,
  simp_rw [trace_iff, mul_apply, std_basis_matrix, mul_boole, ite_and],
  simp only [finset.sum_ite_eq, finset.mem_univ, if_true, ite_mul, zero_mul],
  simp_rw [mul_comm],
end

protected lemma basis_repr_apply [hφ : fact φ.is_faithful_pos_map]
  (x : matrix n n ℂ) (ij : n × n) :
  hφ.elim.basis.repr x ij = ⟪hφ.elim.basis ij, x⟫_ℂ :=
begin
  rw [is_faithful_pos_map.basis_apply, ← is_faithful_pos_map.orthonormal_basis_apply,
    ← orthonormal_basis.repr_apply_apply],
  refl,
end

protected lemma to_matrix_symm_apply
  [hφ : fact φ.is_faithful_pos_map]
  (x : matrix (n × n) (n × n) ℂ) :
  hφ.elim.to_matrix.symm x
    = ∑ (i j k l : n), (x (i,j) (k,l) : ℂ)
      • (|(hφ.elim.basis (i, j))⟩⟨(hφ.elim.basis (k, l))|) :=
begin
  rw [is_faithful_pos_map.to_matrix, linear_map.to_matrix_alg_equiv_symm, linear_map.ext_iff],
  intros a,
  simp_rw [to_lin_alg_equiv_apply, mul_vec, dot_product, is_faithful_pos_map.basis_repr_apply,
    linear_map.sum_apply, linear_map.smul_apply, continuous_linear_map.coe_coe,
    rank_one_apply, is_faithful_pos_map.basis_apply, finset.sum_smul],
  repeat { nth_rewrite_rhs 0 ← finset.sum_product',
    rw [finset.univ_product_univ],
    apply finset.sum_congr rfl,
    intros ij hij, },
  simp_rw [smul_smul, prod.mk.eta],
end

end linear_map.is_faithful_pos_map

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y
lemma linear_map.eq_rank_one_of_faithful_pos_map
  [hφ : fact φ.is_faithful_pos_map]
  (x : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ) :
  x = ∑ i j k l : n, hφ.elim.to_matrix x (i,j) (k,l)
    • (|hφ.elim.basis (i, j)⟩⟨hφ.elim.basis (k, l)|) :=
by rw [← linear_map.is_faithful_pos_map.to_matrix_symm_apply, alg_equiv.symm_apply_apply]

end single_block

---------

section direct_sum

/-! # Section direct_sum -/

namespace linear_map.is_faithful_pos_map

lemma direct_sum_inner_eq [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y : Π i, matrix (s i) (s i) ℂ) :
  ⟪x, y⟫_ℂ = linear_map.direct_sum ψ (star x * y) :=
rfl

lemma direct_sum_inner_eq' [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y : Π i, matrix (s i) (s i) ℂ) :
  ⟪x, y⟫_ℂ = ∑ i, ((ψ i).matrix ⬝ (x i)ᴴ ⬝ y i).trace :=
begin
  simp only [direct_sum_inner_eq, linear_map.direct_sum.linear_functional_eq, pi.mul_apply,
    matrix.mul_eq_mul, matrix.star_eq_conj_transpose, pi.star_apply, matrix.mul_assoc],
end

lemma direct_sum_inner_left_mul [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y z : Π i, matrix (s i) (s i) ℂ) :
  ⟪x * y, z⟫_ℂ = ⟪y, star x * z⟫_ℂ :=
@linear_functional_right_mul _ _ _ _ _ _ (linear_map.direct_sum ψ) _ _ _

lemma direct_sum_linear_functional_mul_right (hψ : Π i, (ψ i).is_faithful_pos_map)
  (x y z : Π i, matrix (s i) (s i) ℂ) :
  linear_map.direct_sum ψ (star x * (y * z))
    = linear_map.direct_sum ψ
      (star (x *
        ((linear_map.direct_sum_matrix_block ψ) * (star z)
          * (linear_map.direct_sum_matrix_block ψ)⁻¹)) * y) :=
begin
  letI := λ i, fact.mk (hψ i),
  rw [← direct_sum_inner_eq],
  simp only [direct_sum_inner_eq'],
  simp_rw [← inner_eq', pi.mul_apply, matrix.mul_eq_mul,
    inner_left_conj, ← direct_sum_inner_eq, inner_direct_sum_eq_sum,
    pi.mul_apply, pi.inv_apply, pi.star_apply, matrix.mul_eq_mul,
    matrix.star_eq_conj_transpose, linear_map.direct_sum_matrix_block_apply],
end

lemma direct_sum_inner_left_conj [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y z : Π i, matrix (s i) (s i) ℂ) :
  ⟪x, y * z⟫_ℂ = ⟪x * ((linear_map.direct_sum_matrix_block ψ) * (star z)
          * (linear_map.direct_sum_matrix_block ψ)⁻¹), y⟫_ℂ :=
direct_sum_linear_functional_mul_right (λ i, (hψ i).elim) _ _ _

lemma direct_sum_inner_right_mul [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y z : Π i, matrix (s i) (s i) ℂ) :
  ⟪x, y * z⟫_ℂ = ⟪star y * x, z⟫_ℂ :=
@linear_functional_left_mul _ _ _ _ _ _ (linear_map.direct_sum ψ) _ _ _

lemma direct_sum_adjoint_eq [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  (linear_map.direct_sum ψ).adjoint
    = algebra.linear_map ℂ (Π i, matrix (s i) (s i) ℂ) :=
begin
  rw linear_map.ext_iff,
  intros x,
  apply @ext_inner_right ℂ,
  intros y,
  rw [linear_map.adjoint_inner_left, algebra.linear_map_apply],
  simp_rw [inner_direct_sum_eq_sum, pi.algebra_map_apply, algebra_map_eq_smul,
    inner_product_space.core.inner_smul_left, inner_eq, conj_transpose_one, matrix.one_mul,
    ← finset.mul_sum],
  refl,
end

protected noncomputable def direct_sum.basis (hψ : Π i, (ψ i).is_faithful_pos_map) :
  basis (Σ i, s i × s i) ℂ (Π i, matrix (s i) (s i) ℂ) :=
pi.basis (λ i, (hψ i).basis)

lemma direct_sum.basis_apply (hψ : Π i, (ψ i).is_faithful_pos_map)
  (ijk : Σ i, s i × s i) :
  direct_sum.basis hψ ijk =
    include_block (std_basis_matrix ijk.2.1 ijk.2.2 1
      ⬝ (hψ ijk.1).matrix_is_pos_def.rpow (-(1/2 : ℝ))) :=
begin
  simp only [direct_sum.basis, pi.basis_apply, function.funext_iff],
  intros i j k,
  simp only [linear_map.std_basis_apply, pi.mul_apply, include_block, linear_map.coe_mk,
    mul_eq_mul, mul_apply, dite_apply, mul_dite, mul_zero, pi.zero_apply,
    function.update],
  rw [dite_eq_iff'],
  split,
  { intros h,
    simp only [h, eq_self_iff_true, dif_pos, linear_map.is_faithful_pos_map.basis_apply],
    finish, },
  { intros h,
    rw eq_comm at h,
    simp only [h, not_false_iff, dif_neg], },
end

lemma direct_sum.basis_apply' (hψ : Π i, (ψ i).is_faithful_pos_map)
  (i : k) (j l : s i) :
  direct_sum.basis hψ ⟨i, (j,l)⟩ =
    include_block (std_basis_matrix j l 1
      ⬝ (hψ i).matrix_is_pos_def.rpow (-(1/2 : ℝ))) :=
direct_sum.basis_apply hψ _

lemma include_block_left_inner [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} (x : matrix (s i) (s i) ℂ)
  (y : Π j, matrix (s j) (s j) ℂ) :
  ⟪include_block x, y⟫_ℂ = ⟪x, y i⟫_ℂ :=
begin
  simp only [inner_direct_sum_eq_sum, include_block_apply,
    linear_map.is_faithful_pos_map.inner_eq', ← mul_eq_mul,
    ← star_eq_conj_transpose, star_dite, star_zero, mul_dite, mul_zero, dite_mul, zero_mul],
  simp_rw [trace_iff, dite_apply, pi.zero_apply, finset.sum_dite_irrel,
    finset.sum_const_zero, finset.sum_dite_eq, finset.mem_univ, if_true],
  refl,
end

lemma include_block_inner_same [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} {x y : matrix (s i) (s i) ℂ} :
  ⟪include_block x, include_block y⟫_ℂ = ⟪x, y⟫_ℂ :=
by rw [include_block_left_inner, include_block_apply_same]

lemma include_block_inner_same' [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i j : k} {x : matrix (s i) (s i) ℂ} {y : matrix (s j) (s j) ℂ} (h : i = j) :
  ⟪include_block x, include_block y⟫_ℂ = ⟪x, (by { rw h, exact y, })⟫_ℂ :=
begin
  simp only [include_block_left_inner, h, include_block_apply, eq_self_iff_true,
    dif_pos],
  refl,
end

lemma include_block_inner_ne_same [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i j : k} {x : matrix (s i) (s i) ℂ}
  {y : matrix (s j) (s j) ℂ} (h : i ≠ j) :
  ⟪include_block x, include_block y⟫_ℂ = 0 :=
begin
  simp only [include_block_left_inner, include_block_apply_ne_same _ h.symm, inner_zero_right],
end

lemma basis.apply_cast_eq_mpr (hψ : Π i, (ψ i).is_faithful_pos_map)
  {i j : k} {a : s j × s j} (h : i = j) :
  (hψ i).basis (by { rw h, exact a, }) =
  by { rw h, exact (hψ j).basis a } :=
begin
  simp only [eq_mpr_eq_cast, h],
  finish,
end

lemma direct_sum.basis_is_orthonormal [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  orthonormal ℂ (direct_sum.basis (λ i, (hψ i).elim)) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [eq_comm, ite_eq_iff'],
  split,
  { rintros rfl,
    simp only [direct_sum.basis_apply, include_block_inner_same', cast_eq, eq_mpr_eq_cast,
      ← linear_map.is_faithful_pos_map.basis_apply, orthonormal_iff_ite.mp basis_is_orthonormal i.snd,
      eq_self_iff_true, if_true], },
  { intros h,
    by_cases h' : i.fst = j.fst,
    { rw [sigma.ext_iff, not_and_distrib] at h,
      cases h with h1 h2,
      { contradiction, },
      { rw [← sigma.eta i, ← sigma.eta j],
        simp only [direct_sum.basis_apply, include_block_inner_same' h',
          ← linear_map.is_faithful_pos_map.basis_apply, ← basis.apply_cast_eq_mpr (λ i, (hψ i).elim),
          sigma.eta, orthonormal_iff_ite.mp basis_is_orthonormal i.snd],
        rw [eq_comm, ite_eq_right_iff],
        intros hh,
        rw hh at h2,
        simp only [eq_mpr_eq_cast, cast_heq, not_true] at h2,
        contradiction, }, },
    { simp only [direct_sum.basis_apply, include_block_inner_ne_same h'], }, },
end

protected noncomputable def direct_sum.orthonormal_basis
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  orthonormal_basis (Σ i, (s i) × (s i)) ℂ (Π i, matrix (s i) (s i) ℂ) :=
basis.to_orthonormal_basis (direct_sum.basis (λ i, (hψ i).elim)) direct_sum.basis_is_orthonormal

lemma direct_sum.orthonormal_basis_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {ijk : Σ i, s i × s i} :
  (direct_sum.orthonormal_basis : orthonormal_basis _ _ _) ijk
    = include_block (std_basis_matrix ijk.2.1 ijk.2.2 1
      ⬝ (hψ ijk.1).elim.matrix_is_pos_def.rpow (-(1/2 : ℝ))) :=
begin
  rw [← direct_sum.basis_apply _],
  simp only [direct_sum.orthonormal_basis, basis.coe_to_orthonormal_basis],
end

lemma direct_sum.orthonormal_basis_apply' [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  {i : k} {j l : s i} :
  (direct_sum.orthonormal_basis : orthonormal_basis _ _ _) ⟨i, (j,l)⟩
    = include_block (std_basis_matrix j l 1
      ⬝ (hψ i).elim.matrix_is_pos_def.rpow (-(1/2 : ℝ))) :=
direct_sum.orthonormal_basis_apply

lemma direct_sum.inner_coord [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (ijk : Σ i, s i × s i) (y : Π i, matrix (s i) (s i) ℂ) :
  ⟪direct_sum.basis (λ i, (hψ i).elim) ijk, y⟫_ℂ
    = ((y ijk.1) ⬝ ((hψ ijk.1).elim.matrix_is_pos_def.rpow (1 / 2))) ijk.2.1 ijk.2.2 :=
begin
  let Q := (ψ ijk.1).matrix,
  let hQ := (hψ ijk.1).elim.matrix_is_pos_def,
  simp_rw [direct_sum.basis_apply, include_block_left_inner,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply, inner_coord],
end

lemma direct_sum.basis_repr_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x : Π i, matrix (s i) (s i) ℂ)
  (ijk : Σ i, s i × s i) :
  (direct_sum.basis (λ i, (hψ i).elim)).repr x ijk
    = ⟪(hψ ijk.1).elim.basis ijk.2, x ijk.1⟫_ℂ :=
begin
  rw [linear_map.is_faithful_pos_map.basis_apply,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply,
    ← orthonormal_basis.repr_apply_apply],
  refl,
end

lemma direct_sum_matrix_block.is_self_adjoint [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  _root_.is_self_adjoint (linear_map.direct_sum_matrix_block ψ) :=
begin
  ext1,
  simp only [pi.star_apply, linear_map.direct_sum_matrix_block_apply,
    star_eq_conj_transpose, (hψ x).elim.matrix_is_pos_def.1.eq],
end

noncomputable def direct_sum_matrix_block_invertible [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  invertible (linear_map.direct_sum_matrix_block ψ) :=
begin
  haveI := λ i, (hψ i).elim.matrix_is_pos_def.invertible,
  apply invertible.mk (linear_map.direct_sum_matrix_block ψ)⁻¹,
  all_goals { ext1,
    simp_rw [pi.mul_apply, pi.inv_apply, linear_map.direct_sum_matrix_block_apply,
      mul_eq_mul, pi.one_apply], },
  work_on_goal 1 { rw [inv_mul_of_invertible], },
  rw [mul_inv_of_invertible],
end

lemma direct_sum_matrix_block_inv_mul_self [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  (linear_map.direct_sum_matrix_block ψ)⁻¹
    * (linear_map.direct_sum_matrix_block ψ) = 1 :=
begin
  haveI := λ i, (hψ i).elim.matrix_is_pos_def.invertible,
  ext1,
  simp_rw [pi.mul_apply, pi.inv_apply, linear_map.direct_sum_matrix_block_apply,
    mul_eq_mul, pi.one_apply, inv_mul_of_invertible],
end
lemma direct_sum_matrix_block_self_mul_inv [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  (linear_map.direct_sum_matrix_block ψ)
    * (linear_map.direct_sum_matrix_block ψ)⁻¹ = 1 :=
begin
  haveI := λ i, (hψ i).elim.matrix_is_pos_def.invertible,
  ext1,
  simp_rw [pi.mul_apply, pi.inv_apply, linear_map.direct_sum_matrix_block_apply,
    mul_eq_mul, pi.one_apply, mul_inv_of_invertible],
end

lemma linear_map.sum_single_comp_proj {R : Type*} {ι : Type*} [fintype ι] [decidable_eq ι] [semiring R] {φ : ι → Type*}
  [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)] :
  ∑ i : ι, linear_map.single i ∘ₗ linear_map.proj i
    = (linear_map.id : (Π i, φ i) →ₗ[R] (Π i, φ i)) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.sum_apply, linear_map.id_apply,
    linear_map.comp_apply, linear_map.proj_apply,
    linear_map.coe_single, pi.single, function.funext_iff,
    finset.sum_apply, function.update, pi.zero_apply,
    finset.sum_dite_eq, finset.mem_univ, if_true],
  intros x y, trivial,
end

lemma linear_map.lrsum_eq_single_proj_lrcomp (f : (Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] (Π i, matrix (s i) (s i) ℂ)) :
  ∑ r p, (linear_map.single r) ∘ₗ (linear_map.proj r) ∘ₗ f
    ∘ₗ (linear_map.single p) ∘ₗ (linear_map.proj p) = f :=
calc ∑ r p, (linear_map.single r) ∘ₗ (linear_map.proj r) ∘ₗ f
    ∘ₗ (linear_map.single p) ∘ₗ (linear_map.proj p)
  = (∑ r, (linear_map.single r) ∘ₗ (linear_map.proj r)) ∘ₗ f
      ∘ₗ ∑ p, (linear_map.single p) ∘ₗ (linear_map.proj p) :
  by simp_rw [linear_map.sum_comp, linear_map.comp_sum, linear_map.comp_assoc]
  ... = linear_map.id ∘ₗ f ∘ₗ linear_map.id : by rw linear_map.sum_single_comp_proj
  ... = f : by rw [linear_map.id_comp, linear_map.comp_id]

@[simps] noncomputable def direct_sum.to_matrix (hψ : Π i, (ψ i).is_faithful_pos_map) :
  ((Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] (Π i, matrix (s i) (s i) ℂ))
    ≃ₐ[ℂ] _  :=
linear_map.to_matrix_alg_equiv (direct_sum.basis hψ)

lemma direct_sum.to_matrix_apply'
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (f : (Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] Π i, matrix (s i) (s i) ℂ)
  (r l : Σ r, s r × s r) :
  (direct_sum.to_matrix (λ i, (hψ i).elim)) f r l
    = (f (include_block ((hψ l.1).elim.basis l.2)) r.1
      ⬝ (hψ r.1).elim.matrix_is_pos_def.rpow (1 / 2)) r.2.1 r.2.2 :=
begin
  simp_rw [direct_sum.to_matrix_apply, linear_map.to_matrix_apply,
    direct_sum.basis_repr_apply, linear_map.is_faithful_pos_map.basis_apply,
    ← linear_map.is_faithful_pos_map.orthonormal_basis_apply, inner_coord,
    direct_sum.basis_apply, linear_map.is_faithful_pos_map.orthonormal_basis_apply],
end

lemma direct_sum_star_alg_equiv_adjoint_eq [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (f : Π i, matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] matrix (s i) (s i) ℂ) (x : Π i, matrix (s i) (s i) ℂ) :
  (star_alg_equiv.direct_sum f).to_alg_equiv.to_linear_map.adjoint x
    = ((star_alg_equiv.direct_sum f).symm
      (x * linear_map.direct_sum_matrix_block ψ))
        * (linear_map.direct_sum_matrix_block ψ)⁻¹ :=
begin
  letI := @direct_sum_matrix_block_invertible _ _ _ _ _ _ ψ _,
  letI := λ i, (hψ i).elim.matrix_is_pos_def.invertible,
  apply @ext_inner_left ℂ,
  intros a,
  simp_rw [linear_map.adjoint_inner_right, alg_equiv.to_linear_map_apply,
    star_alg_equiv.coe_to_alg_equiv],
  rw [← star_alg_equiv.of_direct_sum_matrix_is_inner],
  simp_rw [unitary.inner_aut_star_alg_apply, unitary.inner_aut_star_alg_symm_apply, mul_assoc],
  nth_rewrite_rhs 0 ← mul_assoc (linear_map.direct_sum_matrix_block ψ),
  nth_rewrite_rhs 0 ← mul_assoc,
  rw [direct_sum_inner_left_conj, direct_sum_inner_right_mul],
  simp_rw [star_semigroup.star_mul, is_self_adjoint.star_eq direct_sum_matrix_block.is_self_adjoint, mul_assoc],
  have t1 : linear_map.direct_sum_matrix_block ψ * (linear_map.direct_sum_matrix_block ψ)⁻¹ = 1 :=
  begin
    ext1,
    simp only [pi.mul_apply, pi.inv_apply, mul_eq_mul,
      linear_map.direct_sum_matrix_block_apply, mul_inv_of_invertible, pi.one_apply],
  end,
  have t2 := calc linear_map.direct_sum_matrix_block ψ * star (linear_map.direct_sum_matrix_block ψ)⁻¹
    = linear_map.direct_sum_matrix_block ψ
      * (linear_map.direct_sum_matrix_block ψ)⁻¹ :
  by { congr,
    simp only [pi.inv_def, pi.star_def, linear_map.direct_sum_matrix_block_apply,
      star_eq_conj_transpose, (hψ _).elim.matrix_is_pos_def.1.eq,
      (hψ _).elim.matrix_is_pos_def.inv.1.eq], }
  ... = 1 : t1,
  simp_rw [t1, ← mul_assoc (linear_map.direct_sum_matrix_block ψ), t2, mul_one, one_mul,
    unitary.coe_star, star_star],
end

private lemma mul_inv_eq_iff_eq_mul_aux [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (b c : Π i, matrix (s i) (s i) ℂ) :
  b * (linear_map.direct_sum_matrix_block ψ)⁻¹ = c ↔ b = c * (linear_map.direct_sum_matrix_block ψ) :=
begin
  split,
  { intros h,
    rw [← h, mul_assoc, direct_sum_matrix_block_inv_mul_self, mul_one], },
  { intros h,
    rw [h, mul_assoc, direct_sum_matrix_block_self_mul_inv, mul_one], },
end

lemma star_alg_equiv_direct_sum_is_isometry_tfae [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  [Π i, nontrivial (s i)] (f : Π i, matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] matrix (s i) (s i) ℂ) :
  tfae [(star_alg_equiv.direct_sum f) (linear_map.direct_sum_matrix_block ψ)
    = linear_map.direct_sum_matrix_block ψ,
      (star_alg_equiv.direct_sum f).to_alg_equiv.to_linear_map.adjoint = (star_alg_equiv.direct_sum f).symm.to_alg_equiv.to_linear_map,
    (linear_map.direct_sum ψ) ∘ₗ (star_alg_equiv.direct_sum f).to_alg_equiv.to_linear_map = linear_map.direct_sum ψ,
    ∀ x y, ⟪(star_alg_equiv.direct_sum f) x, (star_alg_equiv.direct_sum f) y⟫_ℂ = ⟪x, y⟫_ℂ,
    ∀ x : Π i, matrix (s i) (s i) ℂ, ‖(star_alg_equiv.direct_sum f) x‖ = ‖x‖] :=
begin
  tfae_have : 5 ↔ 2,
  { simp_rw [inner_product_space.core.norm_eq_sqrt_inner,
    real.sqrt_inj inner_product_space.core.inner_self_nonneg
      inner_product_space.core.inner_self_nonneg, ← complex.of_real_inj,
    inner_self_re, ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ],
    have : ∀ x y, ⟪(star_alg_equiv.direct_sum f) x, (star_alg_equiv.direct_sum f) y⟫_ℂ - ⟪x, y⟫_ℂ
      = ⟪((star_alg_equiv.direct_sum f).to_alg_equiv.to_linear_map.adjoint ∘ₗ (star_alg_equiv.direct_sum f).to_alg_equiv.to_linear_map - 1) x, y⟫_ℂ,
    { intros x y,
      simp only [linear_map.sub_apply, linear_map.one_apply, inner_sub_left,
        linear_map.comp_apply, linear_map.adjoint_inner_left, star_alg_equiv.coe_to_alg_equiv,
        alg_equiv.to_linear_map_apply], },
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, star_alg_equiv.comp_eq_iff,
      linear_map.one_comp], },
  rw tfae_5_iff_2,
  tfae_have : 4 ↔ 3,
  { simp_rw [direct_sum_inner_eq, ← map_star (star_alg_equiv.direct_sum f),
      ← _root_.map_mul (star_alg_equiv.direct_sum f), linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv],
    refine ⟨λ h x, _, λ h x y, h _⟩,
    rw [← one_mul x, ← star_one],
    exact h _ _, },
  rw tfae_4_iff_3,
  letI := @direct_sum_matrix_block_invertible _ _ _ _ _ _ ψ _,
  simp_rw [linear_map.ext_iff, direct_sum_star_alg_equiv_adjoint_eq f, linear_map.comp_apply,
    alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv,
    mul_inv_eq_iff_eq_mul_aux, linear_map.direct_sum.linear_functional_eq'',
    star_alg_equiv.symm_apply_eq, _root_.map_mul,
    star_alg_equiv.apply_symm_apply,
    pi.forall_left_mul, @eq_comm _ (linear_map.direct_sum_matrix_block ψ),
    ← block_diagonal'_alg_hom_apply, ← _root_.map_mul],
  tfae_have : 1 ↔ 2,
  { rw iff_self, trivial, },
  tfae_have : 1 → 3,
  { intros i x,
    nth_rewrite 0 ← i,
    simp_rw [← _root_.map_mul, star_alg_equiv.direct_sum_is_trace_preserving], },
  tfae_have : 3 → 1,
  { intros i,
    simp_rw [← star_alg_equiv.direct_sum_is_trace_preserving
      (λ i, (f i).symm) (linear_map.direct_sum_matrix_block ψ * ((star_alg_equiv.direct_sum f) _)),
      _root_.map_mul, star_alg_equiv.direct_sum_symm_apply_apply, block_diagonal'_alg_hom_apply,
      ← linear_map.direct_sum.linear_functional_eq'',
      @eq_comm _ _ (linear_map.direct_sum ψ _)] at i,
    have := linear_map.linear_functional_direct_sum_eq_of ψ _ i,
    rw [star_alg_equiv.direct_sum_symm_apply_eq] at this,
    exact this.symm, },
  tfae_finish,
end

end linear_map.is_faithful_pos_map

end direct_sum
