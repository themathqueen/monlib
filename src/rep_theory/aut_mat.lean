/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.basic
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.matrix.to_lin
import algebra.module.linear_map
import analysis.inner_product_space.spectrum
import linear_algebra.my_matrix.basic


/-!
# Inner automorphisms

In this file we prove that any algebraic automorphism is an inner automorphism.

We work in a field `is_R_or_C 𝕜` and finite dimensional vector spaces and matrix algebras.

## main definition
`def linear_equiv.matrix_conj_of`: this defines an algebraic automorphism over $Mₙ$ given
  by $x \mapsto yxy^{-1}$ for some linear automorphism $y$ over $\mathbb{k}^n$

## main result
`automorphism_matrix_inner'''`: given an algebraic automorphism $f$ over a non-trivial
  finite-dimensional matrix algebra $M_n(\mathbb{k})$, we have that there exists a
  linear automorphism $T$ over the vector space $\mathbb{k}^n$ such that `f = T.matrix_conj_of`
-/

open_locale big_operators

variables {n R 𝕜 : Type*} [field 𝕜] [fintype n]
local notation `L(`V`)` := V →ₗ[𝕜] V
local notation `M`n := matrix n n 𝕜
local notation `Mₙ`n := matrix n n R

section matrix

open matrix

open_locale matrix

/-- we define `T` as a linear map on `𝕜ⁿ` given by `x ↦ (f (vec_mul_vec x y)) z`,
  where `f` is a linear map on `Mₙ` and `y,z ∈ 𝕜ⁿ` -/
private def mat_T [semiring R] (f : (Mₙ n)→ₗ[R] Mₙ n) (y z : n → R) :
  (n → R) →ₗ[R] (n → R) :=
{ to_fun := λ x, (f (vec_mul_vec x y)).mul_vec z,
  map_add' := λ w p, by { simp_rw [vec_mul_vec_eq, col_add w p,
    matrix.add_mul, map_add, add_mul_vec], },
  map_smul' := λ w r, by { simp_rw [vec_mul_vec_eq, ring_hom.id_apply, col_smul,
    smul_mul, linear_map.map_smul, smul_mul_vec_assoc], } }

private lemma mat_T_apply [semiring R] (f : (Mₙ n) →ₗ[R] Mₙ n) (y z r : n → R) :
  mat_T f y z r = (f (vec_mul_vec r y)).mul_vec z := rfl

-- TODO: generalize this...
/-- any automorphism of `Mₙ` is inner given by `𝕜ⁿ`,
  in particular, given a bijective linear map `f ∈ L(Mₙ)` such that
  `f(ab)=f(a)f(b)`, we have that there exists a matrix `T ∈ Mₙ` such that
  `∀ a ∈ Mₙ : f(a) * T = T * a` and `T` is invertible -/
theorem automorphism_matrix_inner [field R] [decidable_eq n] [nonempty n]
  (f : (Mₙ n) ≃ₐ[R] Mₙ n) :
  ∃ T : Mₙ n, (∀ a : Mₙ n, (f a) ⬝ T = T ⬝ a) ∧ function.bijective T.to_lin' :=
begin
  let hn := _inst_5.some,
  -- there exists a non-zero vector
  have : ∃ u : n → R, u ≠ 0,
  { use pi.has_one.one,
    intros gx,
    simp_rw [function.funext_iff, pi.one_apply, pi.zero_apply] at gx,
    exact one_ne_zero (gx hn), },
  have t1 := this,
  -- let `u, y ∈ 𝕜ⁿ` such that `u,y ≠ 0`
  cases this with u hu,
  cases t1 with y hy,

  -- `f (col u ⬝ (col y)ᴴ) ≠ 0` iff `col u ⬝ (col y)ᴴ ≠ 0`
  -- (and we know `col u ⬝ (col y)ᴴ ≠ 0` since `u,y ≠ 0` by `vec_mul_vec_ne_zero`)
  have f_ne_zero_iff : f (vec_mul_vec u y) ≠ 0 ↔ vec_mul_vec u y ≠ 0,
  { rw not_iff_not,
    exact ⟨λ z, (injective_iff_map_eq_zero f).mp f.bijective.1 _ z,
      λ z, by rw [z, map_zero]⟩, },

  -- there exists a vector `z ∈ 𝕜ⁿ` such that `f (col u ⬝ ) z ≠ 0`
  have : ∃ z : n → R, (f (vec_mul_vec u y)).mul_vec z ≠ 0,
  { simp_rw [ne.def, ← not_forall],
    suffices : ¬ f (vec_mul_vec u y) = 0,
    { simp_rw [mul_vec_eq, zero_mul_vec] at this,
      exact this, },
    rw [← ne.def, f_ne_zero_iff],
    exact vec_mul_vec_ne_zero hu hy, },

  -- let `z ∈ 𝕜ⁿ` such that `f (uy⋆) z ≠ 0`
  cases this with z hz,

  -- let `T ∈ L(𝕜ⁿ)` such that `x ↦ xy⋆ z`
  let T := mat_T f.to_linear_map y z,

  -- we now use `M(T)` as our matrix
  use T.to_matrix',

  -- it is easy to show `(f a) * M(T) = M(T) * a`
  have fir : ∀ a : Mₙ n, (f a) ⬝ T.to_matrix' = T.to_matrix' ⬝ a,
  { simp_rw mul_vec_eq,
    intros A x,
    symmetry,
    calc (T.to_matrix' ⬝ A).mul_vec x = T (A.mul_vec x) :
    by { ext, rw [← mul_vec_mul_vec, linear_map.to_matrix'_mul_vec], }
      ... = (f (vec_mul_vec (A.mul_vec x) y)).mul_vec z :
    by rw [mat_T_apply, alg_equiv.to_linear_map_apply]
      ... = (f (A ⬝ (vec_mul_vec x y))).mul_vec z :
    by simp_rw [vec_mul_vec_eq, col_mul_vec, ← matrix.mul_assoc]
      ... = ((f A) ⬝ (f (vec_mul_vec x y))).mul_vec z :
    by simp_rw [← mul_eq_mul, alg_equiv.map_mul]
      ... = (f A).mul_vec (T x) :
    by simp_rw [← mul_vec_mul_vec, ← alg_equiv.to_linear_map_apply, ← mat_T_apply _ y z]
      ... = ((f A) ⬝ T.to_matrix').mul_vec x :
    by simp_rw [← mul_vec_mul_vec, ← to_lin'_apply T.to_matrix', to_lin'_to_matrix'], },
  refine ⟨fir, _⟩,

  -- we now show `M(T)` is invertible (or, equivalently, `T` is invertible)
  simp_rw to_lin'_to_matrix',

  -- it suffices to show `T` is surjective
  suffices : function.surjective T,
  { exact ⟨linear_map.injective_iff_surjective.mpr this, this⟩ },

  -- let `w ∈ 𝕜ⁿ`
  intros w,

  -- clearly `T u ≠ 0`
  have hi : T u ≠ 0,
  { rw mat_T_apply _ y z,
    exact hz, },

  -- there exists a vector `d ∈ 𝕜ⁿ` such that `(T u) ⬝ d = 1`
  have this1 : ∃ d : n → R, (T u) ⬝ᵥ d = 1,
  { rw ← vec_ne_zero at hi,
    cases hi with q hq,
    use pi.single q (T u q)⁻¹,
    rw [dot_product_single, mul_inv_cancel hq], },

  -- there also exists a matrix `B ∈ Mₙ` such that `(f B) (T u) = w`
  have this2  : ∃ B : Mₙ n, (f B).mul_vec (T u) = w,
  { -- by `this1` we have `d ∈ 𝕜ⁿ` such that `(T u) d = 1`
    cases this1 with d hd,
    -- and since `f` is bijective, we have that there exists a matrix `B` such that
    -- `f B = |w⟩⟨d|`
    cases f.bijective.2 (vec_mul_vec w d) with B hB,
    -- we use this `B` to show our desired result (i.e., `(f B) (T u) = w`)
    -- `(f B) (T u) = wd⋆ * (T u) |w⟩ * d ⬝ (T u) = w = w`
    use B,
    rw [hB, vec_mul_vec_eq, ← mul_vec_mul_vec],
    suffices : (row d).mul_vec (T u) = 1,
    { ext,
      simp_rw [this, mul_vec, dot_product, col_apply, fintype.univ_punit, pi.one_apply, mul_one,
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one, one_mul], },
    ext,
    simp_rw [mul_vec, pi.one_apply, ← hd, dot_product, row_apply, mul_comm], },

  -- now let `B ∈ Mₙ` be our matrix such that `(f B) (T u) = w`
  cases this2 with B hB,
  -- then we let our vector be `M⁻¹(B) u`
  use (B.to_lin' u),
  -- it remains to then show that we have `T (M⁻¹(B) u) = w`
  -- this can be seen from:
  -- `w = (f B) (T u) = (f B) (M(T)u) = ((f B) * M(T)) u = (M(T) * B) u = M(T) (Bu)`
  --             `... = T (M⁻¹(B) u)`
  rw [← to_lin'_to_matrix' T],
  simp_rw [to_lin'_apply, mul_vec_mul_vec, ← fir, ← mul_vec_mul_vec, ← to_lin'_apply T.to_matrix',
    to_lin'_to_matrix'],
  exact hB,
end

private def g_mat [decidable_eq n] (a : M n) (b : (n → 𝕜) → n → 𝕜)
  (hb : function.left_inverse b a.to_lin' ∧ function.right_inverse b a.to_lin') :
  (n → 𝕜) ≃ₗ[𝕜] n → 𝕜 :=
{ to_fun := λ x, a.to_lin' x,
  map_add' := a.to_lin'.map_add',
  map_smul' := a.to_lin'.map_smul',
  inv_fun := b,
  left_inv := hb.1,
  right_inv := hb.2 }

private lemma g_mat_apply [decidable_eq n] (a : M n) (b : (n → 𝕜) → n → 𝕜)
  (hb : function.left_inverse b a.to_lin' ∧ function.right_inverse b a.to_lin')
  (x : n → 𝕜) : g_mat a b hb x = a.to_lin' x := rfl

open_locale matrix

/-- given an automorphic algebraic equivalence `f` on `Mₙ`, we have
  that there exists a linear equivalence `T` such that
  `f(a) = M(T) * a * M(⅟ T)`,
  i.e., any automorphic algebraic equivalence on `Mₙ` is inner -/
lemma automorphism_matrix_inner'' [decidable_eq n] [nonempty n] (f : (M n) ≃ₐ[𝕜] M n) :
  ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
    ∀ a : M n, f a = (T.to_linear_map.to_matrix' ⬝ a) ⬝ T.symm.to_linear_map.to_matrix' :=
begin
  cases automorphism_matrix_inner f with T hT,
  cases function.bijective_iff_has_inverse.mp hT.2 with r hr,
  let g := g_mat T r hr,
  existsi g,
  intro a,
  have : g.to_linear_map = T.to_lin',
  { ext,
    simp_rw [linear_map.coe_comp, linear_equiv.coe_to_linear_map,  linear_map.coe_single,
      function.comp_app, matrix.to_lin'_apply, matrix.mul_vec_single, mul_one, g_mat_apply T r hr,
      matrix.to_lin'_apply, matrix.mul_vec_single, mul_one], },
  rw [this, linear_map.to_matrix'_to_lin', ← hT.1, ← linear_map.to_matrix'_to_lin' T,
    matrix.mul_assoc, ← this],
  symmetry,
  calc (f a) ⬝ (g.to_linear_map.to_matrix' ⬝ g.symm.to_linear_map.to_matrix')
        = (f a) ⬝ (g.to_linear_map ∘ₗ g.symm.to_linear_map).to_matrix' : _
    ... = (f a) ⬝ (g.trans g.symm).to_linear_map.to_matrix' : _
    ... = f a : _,
  simp_rw [linear_map.to_matrix'_comp, linear_equiv.to_linear_map_eq_coe, linear_equiv.comp_coe,
    linear_equiv.symm_trans_self, linear_equiv.self_trans_symm, linear_equiv.self_trans_symm,
    linear_equiv.to_linear_map_eq_coe, linear_equiv.refl_to_linear_map,
    linear_map.to_matrix'_id, matrix.mul_one],
end

def algebra.aut_inner {R E : Type*} [comm_semiring R] [semiring E] [algebra R E]
  (x : E) [invertible x] :
  E ≃ₐ[R] E :=
{ to_fun := λ y, x * y * ⅟ x,
  inv_fun := λ y, ⅟ x * y * x,
  left_inv := λ u, by { simp_rw [← mul_assoc, inv_of_mul_self,
    one_mul, mul_inv_of_mul_self_cancel], },
  right_inv := λ u, by { simp_rw [← mul_assoc, mul_inv_of_self, one_mul,
    mul_mul_inv_of_self_cancel], },
  map_add' := λ y z, by { simp_rw [mul_add, add_mul], },
  commutes' := λ r, by { simp_rw [algebra.algebra_map_eq_smul_one, mul_smul_one,
    smul_mul_assoc, mul_inv_of_self], },
  map_mul' := λ y z, by { simp_rw [mul_assoc, inv_of_mul_self_assoc], } }

lemma algebra.aut_inner_apply {R E : Type*} [comm_semiring R] [semiring E] [algebra R E]
  (x : E) [invertible x] (y : E) :
  (algebra.aut_inner x : E ≃ₐ[R] E) y = x * y * ⅟ x :=
rfl

lemma algebra.aut_inner_symm_apply {R E : Type*} [comm_semiring R] [semiring E] [algebra R E]
  (x : E) [invertible x] (y : E) :
  (algebra.aut_inner x : E ≃ₐ[R] E).symm y = ⅟ x * y * x :=
rfl

lemma algebra.aut_inner_mul_aut_inner {R E : Type*} [comm_semiring R] [semiring E] [algebra R E]
  (x y : E) [invertible x] [invertible y] :
  (algebra.aut_inner x : E ≃ₐ[R] E) * (algebra.aut_inner y)
    = @algebra.aut_inner _ _ _ _ _ (x * y) (_inst_6.mul _inst_7) :=
begin
  ext1,
  simp_rw [alg_equiv.mul_apply, algebra.aut_inner_apply, inv_of_mul, mul_assoc],
end

private lemma automorphism_matrix_inner'''
  [decidable_eq n] [nonempty n] (f : (M n) ≃ₐ[𝕜] M n) :
  ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜, f = @algebra.aut_inner 𝕜 (M n) _ _ _
    (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜).to_matrix' T.to_invertible_matrix :=
begin
  cases automorphism_matrix_inner'' f with T hT,
  existsi T,
  ext,
  simp_rw [algebra.aut_inner_apply, hT],
  refl,
end

theorem aut_mat_inner [decidable_eq n] (f : (M n) ≃ₐ[𝕜] M n) :
  ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜, f = @algebra.aut_inner 𝕜 (M n) _ _ _
    (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜).to_matrix' T.to_invertible_matrix :=
begin
  have hn : nonempty n ∨ ¬ nonempty n := em (nonempty n),
  casesI hn with hn hn,
  { exact automorphism_matrix_inner''' f, },
  { use id,
    { simp_rw [id.def, eq_self_iff_true, forall_const], },
    { simp_rw [id.def, ring_hom.id_apply, eq_self_iff_true, forall_const], },
    { exact id, },
    { intro x, simp only [id.def], },
    { intro x, simp only [id.def], },
    ext,
    simp only [not_nonempty_iff, is_empty_iff, eq_self_iff_true, not_exists, not_true] at hn,
    exfalso,
    exact hn i, },
end

theorem aut_mat_inner' [decidable_eq n] (f : (M n) ≃ₐ[𝕜] M n) :
  ∃ T : GL n 𝕜, f = @algebra.aut_inner 𝕜 (M n) _ _ _ (T : M n) (units.invertible T) :=
begin
  cases aut_mat_inner f with T hT,
  let T' := T.to_linear_map.to_matrix',
  have hT' : T' = T.to_linear_map.to_matrix' := rfl,
  let Tinv := T.symm.to_linear_map.to_matrix',
  have hTinv : Tinv = T.symm.to_linear_map.to_matrix' := rfl,
  refine ⟨⟨T', Tinv, _, _⟩, by congr'⟩,
  all_goals { simp only [matrix.mul_eq_mul, ← linear_map.to_matrix'_mul,
    linear_equiv.to_linear_map_eq_coe, linear_map.mul_eq_comp, linear_equiv.comp_coe,
    linear_equiv.symm_trans_self, linear_equiv.self_trans_symm, linear_equiv.refl_to_linear_map,
    linear_map.to_matrix'_id], },
end

lemma aut_mat_inner_trace_preserving [decidable_eq n] (f : (M n) ≃ₐ[𝕜] M n) (x : M n) :
  (f x).trace = x.trace :=
begin
  obtain ⟨T, rfl⟩ := aut_mat_inner' f,
  rw [algebra.aut_inner_apply, mul_eq_mul, trace_mul_comm, mul_eq_mul,
    matrix.inv_of_mul_self_assoc],
end

/-- if a matrix commutes with all matrices, then it is equal to a scalar
  multiplied by the identity -/
lemma matrix.commutes_with_all_iff {R : Type*} [comm_semiring R]
  [decidable_eq n] {x : matrix n n R} :
  (∀ y : matrix n n R, commute y x) ↔ ∃ α : R, x = α • 1 :=
begin
  simp_rw [commute, semiconj_by, mul_eq_mul],
  split,
  { intros h,
    by_cases h' : x = 0,
    { exact ⟨0, by rw [h', zero_smul]⟩, },
    simp_rw [← eq_zero, not_forall] at h',
    obtain ⟨i, j, hij⟩ := h',
    have : x = diagonal x.diag,
    { ext1 k l,
      specialize h (std_basis_matrix l k 1),
      simp_rw [← matrix.ext_iff, mul_apply, std_basis_matrix, boole_mul, mul_boole,
        ite_and, finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ,
        if_true] at h,
      specialize h k k,
      simp_rw [diagonal, of_apply, matrix.diag],
      simp_rw [eq_self_iff_true, if_true, @eq_comm _ l k] at h,
      exact h.symm, },
    have this1 : ∀ k l : n, x k k = x l l,
    { intros k l,
      specialize h (std_basis_matrix k l 1),
      simp_rw [← matrix.ext_iff, mul_apply, std_basis_matrix, boole_mul, mul_boole,
        ite_and, finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ,
        if_true] at h,
      specialize h k l,
      simp_rw [eq_self_iff_true, if_true] at h,
      exact h.symm, },
    use x i i,
    ext1 k l,
    simp_rw [pi.smul_apply, one_apply, smul_ite, smul_zero, smul_eq_mul, mul_one],
    nth_rewrite_lhs 0 this,
    simp_rw [diagonal, diag, of_apply, this1 i k], },
  { rintros ⟨α, rfl⟩ y,
    simp_rw [matrix.smul_mul, matrix.mul_smul, matrix.one_mul, matrix.mul_one], },
end

private lemma matrix.one_ne_zero {R : Type*} [semiring R] [has_one R] [has_zero R]
  [ne_zero (1 : R)] [decidable_eq n] [nonempty n] :
  (1 : matrix n n R) ≠ 0 :=
begin
  simp_rw [ne.def, ← matrix.eq_zero, matrix.one_apply, ite_eq_right_iff,
    one_ne_zero, imp_false, not_forall, not_not],
  exact ⟨_inst_8.some, _inst_8.some, rfl⟩,
end

lemma matrix.commutes_with_all_iff_of_ne_zero [decidable_eq n] [nonempty n] {x : matrix n n 𝕜}
  (hx : x ≠ 0) :
  (∀ y : matrix n n 𝕜, commute y x) ↔ ∃! α : 𝕜ˣ, x = (α : 𝕜) • 1 :=
begin
  simp_rw [matrix.commutes_with_all_iff],
  refine ⟨λ h, _, λ ⟨α, hα, h⟩, ⟨α, hα⟩⟩,
  obtain ⟨α, hα⟩ := h,
  have : α ≠ 0,
  { intros this,
    rw [this, zero_smul] at hα,
    contradiction, },
  refine ⟨units.mk0 α this, hα, λ y hy, _⟩,
  simp only at hy,
  rw [hα, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy,
  simp_rw [matrix.one_ne_zero, or_false] at hy,
  simp_rw [units.mk0, hy, units.mk_coe],
end

lemma algebra.aut_inner_eq_aut_inner_iff [decidable_eq n] [nonempty n]
  (x y : matrix n n 𝕜) [invertible x] [invertible y] :
  (algebra.aut_inner x : matrix n n 𝕜 ≃ₐ[𝕜] matrix n n 𝕜) = algebra.aut_inner y
    ↔ ∃ α : 𝕜, y = α • x :=
begin
  have : (∃ (α : 𝕜), y = α • x) ↔ ∃ α : 𝕜, ⅟ x * y = α • 1,
  { simp_rw [inv_of_eq_nonsing_inv, mul_eq_mul, inv_mul_eq_iff_eq_mul_of_invertible,
      matrix.mul_smul, matrix.mul_one], },
  simp_rw [this, alg_equiv.ext_iff, algebra.aut_inner_apply, ← matrix.commutes_with_all_iff,
    commute, semiconj_by, inv_of_eq_nonsing_inv, mul_eq_mul,
    ← mul_inv_eq_iff_eq_mul_of_invertible, matrix.mul_assoc, ← inv_mul_eq_iff_eq_mul_of_invertible,
    inv_inv_of_invertible],
end

end matrix
