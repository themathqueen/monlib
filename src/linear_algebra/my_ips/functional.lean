/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.pos_eq_linear_map_is_positive
import preq.is_R_or_C_le
import linear_algebra.is_real
import linear_algebra.my_matrix.include_block

/-!

# Linear functionals

This file contains results for linear functionals on the set of $n \times n$ matrices $M_n$ over $\mathbb{C}$.

## Main results
- `module.dual.apply`
- `module.dual.is_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff`
- `module.dual.is_tracial_faithful_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff_is_inner`

-/

variables {𝕜 R n : Type*} [is_R_or_C 𝕜] [comm_semiring R] [fintype n] [decidable_eq n]

open_locale matrix big_operators
open matrix

/-- the matrix of a linear map `φ : M_n →ₗ[R] R` is given by
  `∑ i j, std_basis_matrix j i (φ (std_basis_matrix i j 1))`. -/
def module.dual.matrix (φ : module.dual R (matrix n n R)) :=
∑ i j : n, matrix.std_basis_matrix j i (φ (matrix.std_basis_matrix i j 1))

/-- given any linear functional `φ : M_n →ₗ[R] R`, we get `φ a = (φ.matrix ⬝ a).trace`. -/
lemma module.dual.apply (φ : module.dual R (matrix n n R)) (a : matrix n n R) :
  φ a = (φ.matrix ⬝ a).trace :=
begin
  simp_rw [module.dual.matrix, smul_std_basis_matrix' _ _ (φ _)],
  simp_rw [matrix.sum_mul, matrix.smul_mul, trace_sum, trace_smul, matrix.trace, matrix.diag,
    mul_apply, std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
    finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, ← ite_and,
    smul_eq_mul, mul_comm (φ _) _, ← smul_eq_mul, ← smul_hom_class.map_smul,
    ← map_sum],
  have : ∀ ⦃i : n⦄ ⦃j : n⦄ ⦃a : R⦄, std_basis_matrix i j (a : R)
    = λ k l, (ite (i = k ∧ j = l) (a : R) (0 : R)) := λ i j a, rfl,
  simp_rw [← this, smul_std_basis_matrix, smul_eq_mul, mul_one],
  rw [← matrix_eq_sum_std_basis a],
end

/-- we linear maps `φ_i : M_[n_i] →ₗ[R] R`, we define its direct sum as the linear map `(Π i, M_[n_i]) →ₗ[R] R`. -/
@[simps] def module.dual.pi {k : Type*} [fintype k]
  {s : k → Type*}
  (φ : Π i, module.dual R (matrix (s i) (s i) R)):
  module.dual R (Π i, matrix (s i) (s i) R) :=
{ to_fun := λ a, ∑ i : k, φ i (a i),
  map_add' := λ x y, by simp only [map_add, pi.add_apply, finset.sum_add_distrib],
  map_smul' := λ r x, by simp only [smul_hom_class.map_smul, pi.smul_apply,
    finset.smul_sum, ring_hom.id_apply], }

/-- for direct sums, we get `φ x = ∑ i, ((φ i).matrix ⬝ x i).trace` -/
lemma module.dual.pi.apply {k : Type*} [fintype k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, module.dual R (matrix (s i) (s i) R))
  (x : Π i, matrix (s i) (s i) R) :
  module.dual.pi φ x = ∑ i, ((φ i).matrix ⬝ x i).trace :=
begin
  simp_rw [module.dual.pi_apply, module.dual.apply],
end

lemma module.dual.pi.apply' {k : Type*} [fintype k]
  [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, module.dual R (matrix (s i) (s i) R)) (x : Π i, matrix (s i) (s i) R) :
  module.dual.pi φ x = ∑ i, (block_diagonal' (φ i).matrix.include_block ⬝ block_diagonal' x).trace :=
begin
  symmetry,
  simp_rw [← block_diagonal'_mul, ← mul_eq_mul],
  calc ∑ (x_1 : k), (block_diagonal'
    (λ (k_1 : k), (φ x_1).matrix.include_block k_1 * x k_1)).trace
    = ∑ (x_1 : k), (block_diagonal' (λ k_1, ((φ x_1).matrix.include_block * x) k_1)).trace : rfl
  ... = ∑ (x_1 : k), (block_diagonal' (λ k_1, ((φ x_1).matrix * x x_1).include_block k_1)).trace :
  by { congr,
    ext,
    congr,
    ext,
    simp only [include_block_mul], }
  ... = ∑ x_1, ((φ x_1).matrix * x x_1).trace :
  by {
    simp only [include_block_apply, trace_iff,
      block_diagonal'_apply, dite_apply, eq_self_iff_true, dif_pos,
      pi.zero_apply, eq_mp_eq_cast, cast_eq],
    rw finset.sum_comm,
    simp only [finset.sum_dite_eq', finset.mem_univ, if_true],
    simp_rw [finset.sum_sigma'],
    refl, }
  ... = module.dual.pi φ x : (module.dual.pi.apply _ _).symm,
end

lemma module.dual.apply_eq_of
  (φ : module.dual R (matrix n n R)) (x : matrix n n R)
  (h : ∀ a, φ a = (x ⬝ a).trace) :
  x = φ.matrix :=
begin
  simp_rw [module.dual.apply, ← matrix.ext_iff_trace] at h,
  exact h.symm,
end

/-- Any linear functional $f$ on $M_n$ is given by a unique matrix $Q \in M_n$ such that $f(x)=\operatorname{Tr}(Qx)$ for any $x \in M_n$. -/
lemma module.dual.eq_trace_unique (φ : module.dual R (matrix n n R)) :
  ∃! Q : matrix n n R, ∀ a : matrix n n R, φ a = (Q ⬝ a).trace :=
begin
  use φ.matrix,
  simp_rw [module.dual.apply, eq_self_iff_true, forall_true_iff, true_and, ← matrix.ext_iff_trace, eq_comm,
    imp_self, forall_true_iff],
end

def module.dual.pi' {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, module.dual R (matrix (s i) (s i) R)) :
  module.dual R { x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal } :=
(module.dual.pi φ) ∘ₗ is_block_diagonal_pi_alg_equiv.to_linear_map

/-- `⨁_i φ_i ι_i (x_i) = φ_i (x_i)` -/
lemma module.dual.pi.apply_single_block {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R) (x : Π i, matrix (s i) (s i) R)
  (i : k) :
  (module.dual.pi φ) (include_block (x i)) = φ i (x i) :=
begin
  simp_rw [module.dual.pi_apply, module.dual.apply,
    include_block_apply, ←mul_eq_mul, mul_dite,
    mul_zero, trace_iff, dite_apply, pi.zero_apply,
    finset.sum_dite_irrel, finset.sum_const_zero, finset.sum_dite_eq,
    finset.mem_univ, if_true],
  refl,
end

open_locale complex_order
open_locale direct_sum
/-- A linear functional $φ$ on $M_n$ is positive if $0 ≤ φ (x^*x)$ for all $x \in M_n$. -/
def module.dual.is_pos_map {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : module.dual 𝕜 A) : Prop :=
∀ a : A, 0 ≤ φ (star a * a)

/-- A linear functional $φ$ on $M_n$ is unital if $φ(1) = 1$. -/
def module.dual.is_unital {A : Type*} [add_comm_monoid A] [module R A] [has_one A]
  (φ : module.dual R A) : Prop :=
φ (1 : A) = 1

/-- A linear functional is called a state if it is positive and unital -/
def module.dual.is_state {A : Type*} [semiring A] [star_ring A] [module 𝕜 A] (φ : module.dual 𝕜 A) :
  Prop :=
φ.is_pos_map ∧ φ.is_unital

lemma module.dual.is_pos_map_of_matrix (φ : module.dual 𝕜 (matrix n n 𝕜)) :
  φ.is_pos_map ↔ (∀ a : matrix n n 𝕜, a.pos_semidef → 0 ≤ φ a) :=
begin
  simp_rw [pos_semidef_iff, exists_imp_distrib, module.dual.is_pos_map,
    mul_eq_mul, forall_eq_apply_imp_iff', star_eq_conj_transpose],
end

/-- A linear functional $f$ on $M_n$ is said to be faithful if $f(x^*x)=0$ if and only if $x=0$ for any $x \in M_n$. -/
def module.dual.is_faithful {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : module.dual 𝕜 A) : Prop :=
∀ a : A, φ (star a * a) = 0 ↔ a = 0

lemma module.dual.is_faithful_of_matrix (φ : module.dual 𝕜 (matrix n n 𝕜)) :
  φ.is_faithful ↔ (∀ a : matrix n n 𝕜, a.pos_semidef → (φ a = 0 ↔ a = 0)) :=
begin
  simp_rw [pos_semidef_iff, exists_imp_distrib,
    module.dual.is_faithful, mul_eq_mul, forall_eq_apply_imp_iff',
    conj_transpose_mul_self_eq_zero, star_eq_conj_transpose],
end

/-- A linear functional $f$ is positive if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$.  -/
lemma module.dual.is_pos_map_iff_of_matrix (φ : module.dual ℂ (matrix n n ℂ)) :
  φ.is_pos_map ↔ φ.matrix.pos_semidef :=
begin
  split,
  { intros hs,
    rw [module.dual.is_pos_map_of_matrix] at hs,
    simp only [module.dual.apply] at hs,
    have thiseq : ∀ y, star y ⬝ᵥ φ.matrix.mul_vec y = (φ.matrix ⬝ vec_mul_vec y (star y)).trace,
    { intros y,
      rw [vec_mul_vec_eq, trace_mul_cycle', ← col_mul_vec],
      simp_rw [matrix.trace_iff', row_mul_col_apply, fintype.univ_punit,
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one, one_mul], },
      simp_rw [pos_semidef.complex, thiseq],
      intros y,
      -- rw [thiseq, ← is_R_or_C.re_to_complex, ← is_R_or_C.nonneg_def'],
      refine hs _ _,
      exact vec_mul_vec.pos_semidef _, },
  { intros hy y,
    rw [φ.apply, mul_eq_mul, ← matrix.mul_assoc, is_R_or_C.nonneg_def'],
    exact hy.trace_conj_transpose_mul_self_nonneg _, },
end

/-- A linear functional $f$ is a state if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such that its trace equals $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma module.dual.is_state_iff_of_matrix
  (φ : module.dual ℂ (matrix n n ℂ)) :
  φ.is_state ↔ φ.matrix.pos_semidef ∧ φ.matrix.trace = 1 :=
begin
  rw [module.dual.is_state, module.dual.is_pos_map_iff_of_matrix, module.dual.is_unital,
    module.dual.apply, matrix.mul_one],
end

/-- A positive linear functional $f$ is faithful if and only if there exists a positive definite matrix such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma module.dual.is_pos_map.is_faithful_iff_of_matrix
  {φ : module.dual ℂ (matrix n n ℂ)} (hs : φ.is_pos_map) :
  φ.is_faithful ↔ φ.matrix.pos_def :=
begin
  have hs' := hs,
  rw [module.dual.is_pos_map_of_matrix] at hs',
  rw module.dual.is_faithful_of_matrix,
  split,
  { rw module.dual.is_pos_map_iff_of_matrix at hs,
    intros HHH,
    { refine ⟨hs.1, _⟩,
      intros x hx,
      have : star x ⬝ᵥ φ.matrix.mul_vec x = (φ.matrix ⬝ vec_mul_vec x (star x)).trace,
      { rw [vec_mul_vec_eq, trace_mul_cycle', ← col_mul_vec],
        simp_rw [matrix.trace_iff', row_mul_col_apply, fintype.univ_punit,
          finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one, one_mul], },
      rw [this],
      have this2 := HHH (vec_mul_vec x (star x)) (vec_mul_vec.pos_semidef _),
      have this3 := (hs' (vec_mul_vec x (star x)) (vec_mul_vec.pos_semidef _)),
      rw [le_iff_eq_or_lt] at this3,
      rcases this3 with (this3 | this32),
      { rw [eq_comm, this3, this2, vec_mul_vec_eq_zero_iff] at this3,
        contradiction, },
      { rw ← module.dual.apply,
        exact (is_R_or_C.pos_def.mp this32).1, }, }, },
  { intros hQ a ha,
    refine ⟨λ h, _, λ h, by rw [h, map_zero]⟩,
    obtain ⟨b, rfl⟩ := (pos_semidef_iff _).mp ha,
    rw [module.dual.apply, ← matrix.mul_assoc,
      nontracial.trace_conj_transpose_mul_self_eq_zero hQ] at h,
    rw [h, matrix.mul_zero], },
end

def module.dual.is_faithful_pos_map {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : module.dual 𝕜 A) : Prop :=
φ.is_pos_map ∧ φ.is_faithful

/-- A linear functional $φ$ is a faithful and positive if and only if there exists a unique positive definite matrix $Q$ such that $φ(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma module.dual.is_faithful_pos_map_iff_of_matrix (φ : module.dual ℂ (matrix n n ℂ)) :
  φ.is_faithful_pos_map ↔ φ.matrix.pos_def :=
begin
  refine ⟨λ h, h.1.is_faithful_iff_of_matrix.mp h.2, _⟩,
  intros hQ,
  simp_rw [module.dual.is_faithful_pos_map, module.dual.is_faithful,
    module.dual.is_pos_map_iff_of_matrix, hQ.pos_semidef, true_and,
    module.dual.apply, mul_eq_mul, star_eq_conj_transpose, ← matrix.mul_assoc,
    nontracial.trace_conj_transpose_mul_self_eq_zero hQ, iff_self, forall_const],
end

/-- A state is faithful $f$ if and only if there exists a unique positive definite matrix $Q\in M_n$ with trace equal to $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x \in M_n$. -/
lemma  module.dual.is_state.is_faithful_iff_of_matrix {φ : module.dual ℂ (matrix n n ℂ)}
  (hs : φ.is_state) :
  φ.is_faithful ↔ φ.matrix.pos_def ∧ φ.matrix.trace = 1 :=
begin
  rw hs.1.is_faithful_iff_of_matrix,
  refine ⟨λ hQ, ⟨hQ,_⟩, λ hQ, hQ.1⟩,
  { rw [module.dual.is_state_iff_of_matrix] at hs,
    exact hs.2, },
end

lemma module.dual.is_faithful_state_iff_of_matrix (φ : module.dual ℂ (matrix n n ℂ)) :
  (φ.is_state ∧ φ.is_faithful)
    ↔ φ.matrix.pos_def ∧ φ.matrix.trace = 1 :=
begin
  refine ⟨λ h, h.1.is_faithful_iff_of_matrix.mp h.2, _⟩,
  intros hQ,
  simp_rw [module.dual.is_faithful, module.dual.is_state_iff_of_matrix, hQ.2, hQ.1.pos_semidef,
    eq_self_iff_true, true_and],
  rw ← module.dual.is_faithful_pos_map_iff_of_matrix at hQ,
  exact hQ.1.2,
end

/-- A linear functional $f$ is tracial if and only if $f(xy)=f(yx)$ for all $x,y$. -/
def module.dual.is_tracial  {A : Type*} [non_unital_semiring A]
  [module 𝕜 A] (φ : module.dual 𝕜 A) :
  Prop :=
∀ x y : A, φ (x * y) = φ (y * x)

/-- A linear functional is tracial and positive if and only if there exists a non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
lemma module.dual.is_tracial_pos_map_iff_of_matrix (φ : module.dual ℂ (matrix n n ℂ)) :
  (φ.is_pos_map ∧ φ.is_tracial) ↔ ∃ α : nnreal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
begin
  split,
  { simp_rw [module.dual.is_pos_map_iff_of_matrix],
    rintros ⟨hQ, h2⟩,
    simp_rw [module.dual.is_tracial, module.dual.apply,
      matrix.trace, matrix.diag, mul_eq_mul, mul_apply] at h2,
    let Q := φ.matrix,
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 :=
    λ p q r, calc Q p q = ∑ i j, Q i j
      * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :
    by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
      finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, eq_self_iff_true, if_true,
      mul_ite, mul_zero, mul_one], }
      ... = ∑ i j, Q i j
      * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i : by rw h2
      ... = ite (p = q) (Q r r) 0 :
    by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
      finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, mul_ite,
      mul_zero, mul_one], },
    by_cases h : is_empty n,
    { use 1,
      haveI := h,
      simp only [eq_iff_true_of_subsingleton], },
    rw not_is_empty_iff at h,
    let i : n := h.some,
    have HH : Q = diagonal (λ (x_1 : n), Q i i),
    { ext1,
      exact this _ _ i, },
    have this' : ∀ p, Q p p = is_R_or_C.re (Q p p),
    { intros p,
      rw [eq_comm, ← is_R_or_C.conj_eq_iff_re, ← is_R_or_C.star_def, ← matrix.star_apply,
        star_eq_conj_transpose, hQ.1.eq], },
    have : 0 ≤ (Q i i),
    { rw pos_semidef.complex at hQ,
      specialize hQ (λ j, ite (i = j) 1 0),
      simp_rw [dot_product, mul_vec, dot_product, pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at hQ,
      exact hQ, },
    have thisthis : 0 ≤ is_R_or_C.re (Q i i) :=
    by { rw [is_R_or_C.nonneg_def'] at this,
      exact this.2, },
    let α : nnreal := ⟨is_R_or_C.re (Q i i), thisthis⟩,
    have hα : (α : ℂ) = is_R_or_C.re (Q i i) := rfl,
    have hα' : is_R_or_C.re (Q i i) = α := rfl,
    refine ⟨α, _⟩,
    { simp only [smul_eq_diagonal_mul, ← hα', matrix.mul_one],
      rw ← this',
      exact HH, }, },
  { rintros ⟨α, hα1⟩,
    simp_rw [module.dual.is_pos_map, module.dual.is_tracial, module.dual.apply,
      hα1, is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply, matrix.smul_mul, matrix.one_mul, trace_star, conj_transpose_smul,
      mul_eq_mul, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose, is_R_or_C.star_def, is_R_or_C.conj_of_real,
      trace_smul, smul_eq_mul, is_R_or_C.of_real_mul_re, mul_nonneg (nnreal.coe_nonneg _)
        (trace_conj_transpose_mul_self_re_nonneg _), and_true],
    exact ⟨λ _, rfl, λ _ _, by rw trace_mul_comm⟩, },
end


/-- A linear functional is tracial and positive if and only if there exists a unique non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
lemma module.dual.is_tracial_pos_map_iff'_of_matrix [nonempty n]
  (φ : module.dual ℂ (matrix n n ℂ)) :
  (φ.is_pos_map ∧ φ.is_tracial) ↔ ∃! α : nnreal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
begin
  split,
  { simp_rw [module.dual.is_pos_map_iff_of_matrix],
    rintros ⟨hQ, h2⟩,
    simp_rw [module.dual.is_tracial, module.dual.apply,
      matrix.trace, matrix.diag, mul_eq_mul, mul_apply] at h2,
    let Q := φ.matrix,
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 :=
    λ p q r, calc Q p q = ∑ i j, Q i j
      * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :
    by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
      finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, eq_self_iff_true, if_true,
      mul_ite, mul_zero, mul_one], }
      ... = ∑ i j, Q i j
      * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i : by rw h2
      ... = ite (p = q) (Q r r) 0 :
    by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
      finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, mul_ite,
      mul_zero, mul_one], },
    let i : n := _inst_5.some,
    have HH : Q = diagonal (λ (x_1 : n), Q i i),
    { ext1,
      exact this _ _ i, },
    have this' : ∀ p, Q p p = is_R_or_C.re (Q p p),
    { intros p,
      rw [eq_comm, ← is_R_or_C.conj_eq_iff_re, ← is_R_or_C.star_def, ← matrix.star_apply,
        star_eq_conj_transpose, hQ.1.eq], },
    have : 0 ≤ (Q i i),
    { rw pos_semidef.complex at hQ,
      specialize hQ (λ j, ite (i = j) 1 0),
      simp_rw [dot_product, mul_vec, dot_product, pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at hQ,
      exact hQ, },
    have thisthis: 0 ≤ is_R_or_C.re (Q i i) :=
    by { rw [is_R_or_C.nonneg_def'] at this,
      exact this.2, }, 
    let α : nnreal := ⟨is_R_or_C.re (Q i i), thisthis⟩,
    have hα : (α : ℂ) = is_R_or_C.re (Q i i) := rfl,
    have hα' : is_R_or_C.re (Q i i) = α := rfl,
    refine ⟨α, ⟨_, _⟩⟩,
    { simp only [smul_eq_diagonal_mul, ← hα', matrix.mul_one],
      rw ← this',
      exact HH, },
    { intros y hy,
      simp only [Q] at *,
      simp only [smul_eq_diagonal_mul, matrix.mul_one] at hy,
      rw [HH, diagonal_eq_diagonal_iff, this'] at hy,
      specialize hy i,
      norm_cast at hy,
      simp_rw [α, Q, hy, subtype.coe_eta], }, },
  { rintros ⟨α, ⟨hα1, hα2⟩⟩,
    simp_rw [module.dual.is_pos_map, module.dual.is_tracial, module.dual.apply,
      hα1, is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply, matrix.smul_mul, matrix.one_mul, trace_star, conj_transpose_smul,
      mul_eq_mul, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose, is_R_or_C.star_def, is_R_or_C.conj_of_real,
      trace_smul, smul_eq_mul, is_R_or_C.of_real_mul_re, mul_nonneg (nnreal.coe_nonneg _)
        (trace_conj_transpose_mul_self_re_nonneg _), and_true],
    exact ⟨λ _, rfl, λ _ _, by rw trace_mul_comm⟩, },
end

/-- A linear functional $f$ is tracial positive and faithful if and only if there exists a positive real number $\alpha$ such that $f\colon x\mapsto \alpha \operatorname{Tr}(x)$. -/
lemma module.dual.is_tracial_faithful_pos_map_iff_of_matrix [nonempty n]
  (φ : module.dual ℂ (matrix n n ℂ)) :
  (φ.is_faithful_pos_map ∧ φ.is_tracial)
    ↔ ∃! α : {x : nnreal // 0 < x}, φ.matrix = (((α : nnreal) : ℝ) : ℂ) • 1 :=
begin
  rw [module.dual.is_faithful_pos_map, and_comm φ.is_pos_map _, and_assoc,
    module.dual.is_tracial_pos_map_iff'_of_matrix],
  split,
  { rintros ⟨h1, ⟨α, hα, h⟩⟩,
    have : 0 < (α : ℝ) :=
    by { rw [nnreal.coe_pos, pos_iff_ne_zero],
      intros HH,
      rw module.dual.is_faithful at h1,
      specialize h1 ((1 : matrix n n ℂ)ᴴ ⬝ (1 : matrix n n ℂ)),
      simp only [matrix.conj_transpose_one, matrix.one_mul, matrix.mul_one,
        module.dual.apply, mul_eq_mul, star_eq_conj_transpose] at h1,
      simp_rw [HH, nnreal.coe_zero, complex.of_real_zero, zero_smul] at hα,
      rw [hα, trace_zero, eq_self_iff_true, true_iff] at h1,
      simp only [one_ne_zero'] at h1,
      exact h1, },
    let α' : {x : nnreal // 0 < x} := ⟨α, this⟩,
    have : α = α' := rfl,
    refine ⟨α', hα, λ y hy, _⟩,
    simp_rw [← subtype.coe_inj, subtype.coe_mk] at hy ⊢,
    norm_cast,
    exact h _ hy, },
  { rintros ⟨α, ⟨h1, h2⟩⟩,
    have : 0 < (α : nnreal) := subtype.mem α,
    refine ⟨_, ⟨α, h1, λ y hy, _⟩⟩,
    { simp_rw [module.dual.is_faithful, module.dual.apply, h1,
        matrix.smul_mul, matrix.one_mul, trace_smul, smul_eq_zero,
        is_R_or_C.of_real_eq_zero, nnreal.coe_eq_zero, ne_zero_of_lt this,
        false_or, star_eq_conj_transpose, mul_eq_mul, trace_conj_transpose_mul_self_eq_zero,
        iff_self, forall_true_iff], },
    rw [h1, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy,
    simp only [one_ne_zero', or_false, is_R_or_C.of_real_inj, nnreal.coe_eq] at hy,
    rw hy, },
end

-- lemma linear_map.is_tracial_state_iff [nonempty n] (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
--   (φ.is_state ∧ φ.is_tracial) ↔ ∃ α : ℂ, φ.matrix = α • 1 ∧ α * (1 : matrix n n ℂ).trace = 1 :=
-- begin
--   split,
--   { simp_rw [linear_map.is_state_iff],
--     -- rintros ⟨⟨Q, ⟨hQ1, hQ2, hQ3⟩, h1⟩, h2⟩,
--     simp_rw [linear_map.is_tracial, hQ3, matrix.trace, matrix.diag, mul_apply] at h2,
--     have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 :=
--     λ p q r, calc Q p q = ∑ i j, Q i j
--       * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :
--     by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
--       finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, eq_self_iff_true, if_true,
--       mul_ite, mul_zero, mul_one], }
--       ... = ∑ i j, Q i j
--       * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i : by rw h2
--       ... = ite (p = q) (Q r r) 0 :
--     by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
--       finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, mul_ite,
--       mul_zero, mul_one], },
--     let i : n := _inst_5.some,
--     use Q i i,
--     simp_rw [trace_one, ← hQ2],
--     split,
--     { intros x,
--       simp_rw [hQ3, matrix.trace, matrix.diag, mul_apply],
--       calc ∑ k j, Q k j * x j k = ∑ k j, ite (k = j) (Q i i) 0 * x j k : by simp_rw ← this _ _ i
--         ... = Q i i * ∑ k, x k k : _,
--       simp_rw [ite_mul, zero_mul, finset.sum_ite_eq, finset.mem_univ, if_true,
--         finset.mul_sum], },
--     { rw eq_comm,
--       calc ∑ k, Q k k = ∑ k : n, ite (k = k) (Q i i) 0 : by simp_rw ← this _ _ i
--         ... = ∑ k : n, Q i i : by simp_rw [eq_self_iff_true, if_true]
--         ... = Q i i * ↑(fintype.card n) : _,
--       simp_rw [finset.sum_const, nsmul_eq_mul, mul_comm],
--       refl, }, },
--   { rintros ⟨α, ⟨hα1, hα2⟩⟩,
--     simp_rw [linear_map.is_state_iff, hα1],
--     split,
--     { use α • 1,
--       split,
--       { simp only [matrix.smul_mul, trace_smul, smul_eq_mul, matrix.one_mul],
--         refine ⟨_, hα2, λ _, rfl⟩,
--         simp only [← diagonal_one, ← diagonal_smul, pos_semidef.diagonal],
--         intros i,
--         simp_rw [pi.smul_apply, ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply,
--           smul_eq_mul, mul_one],
--         have : α = 1 / (1 : matrix n n ℂ).trace,
--         { rw [← hα2, trace_one, ← mul_div, div_self, mul_one],
--           { simp only [ne.def, nat.cast_eq_zero],
--             exact fintype.card_ne_zero, }, },
--         simp_rw [this, trace_one, star_div', star_one, star_nat_cast, eq_self_iff_true, and_true],
--         simp only [one_div, is_R_or_C.re_to_complex, complex.inv_re, complex.nat_cast_re],
--         apply div_nonneg,
--         { exact (nat.cast_nonneg _), },
--         { simp_rw [complex.norm_sq_nonneg], }, },
--       { simp only,
--         rintros y ⟨hy1, hy2, hy3⟩,
--         ext1 i j,
--         simp_rw [pi.smul_apply, one_apply, smul_eq_mul, mul_boole],
--         specialize hy3 (std_basis_matrix j i (1 : ℂ)),
--         simp_rw [std_basis_matrix.trace, matrix.trace, matrix.diag, mul_apply,
--           std_basis_matrix, mul_boole, ite_and] at hy3,
--         simp only [finset.sum_ite_eq, finset.mem_univ, if_true] at hy3,
--         simp_rw @eq_comm _ j i at hy3,
--         exact hy3.symm, }, },
--     { intros x y,
--       rw [hα1, trace_mul_comm, ← hα1], }, },
-- end

lemma matrix.ext_iff_trace' {R m n : Type*}
  [semiring R] [star_ring R] [fintype n] [fintype m]
  [decidable_eq n] [decidable_eq m]
  (A B : matrix m n R) :
  (∀ x, (xᴴ ⬝ A).trace = (xᴴ ⬝ B).trace) ↔ A = B :=
begin
  refine ⟨λ h, _, λ h x, by rw [h]⟩,
  ext i j,
  specialize h (std_basis_matrix i j (1 : R)),
  simp_rw [std_basis_matrix_conj_transpose,
    star_one, matrix.std_basis_matrix_mul_trace] at h,
  exact h,
end

lemma module.dual.is_real_iff {φ : module.dual ℂ (matrix n n ℂ)} :
  φ.is_real ↔ φ.matrix.is_hermitian :=
begin
  simp_rw [linear_map.is_real, module.dual.apply,
    trace_star, conj_transpose_mul,
    star_eq_conj_transpose, trace_mul_comm (φ.matrix),
    matrix.ext_iff_trace', is_hermitian, eq_comm],
end

lemma module.dual.is_pos_map.is_real {φ : module.dual ℂ (matrix n n ℂ)}
  (hφ : φ.is_pos_map) :
  φ.is_real :=
begin
  rw module.dual.is_pos_map_iff_of_matrix at hφ,
  rw [module.dual.is_real_iff],
  exact hφ.1,
end

lemma module.dual.pi.is_pos_map.is_real {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)} (hψ : Π i, (ψ i).is_pos_map) :
  (module.dual.pi ψ).is_real :=
begin
  simp_rw [linear_map.is_real, module.dual.pi_apply, star_sum, pi.star_apply,
    (hψ _).is_real _, eq_self_iff_true, forall_true_iff],
end

/-- A function $H \times H \to 𝕜$ defines an inner product if it satisfies the following. -/
def is_inner {H : Type*} [add_comm_monoid H] [module 𝕜 H] (φ : H×H → 𝕜) : Prop :=
(∀ x y : H, φ (x, y) = star (φ (y, x)))
  ∧ (∀ x : H, 0 ≤ is_R_or_C.re (φ (x, x)))
  ∧ (∀ x : H, φ (x, x) = 0 ↔ x = 0)
  ∧ (∀ x y z : H, φ (x+y, z) = φ (x, z) + φ (y, z))
  ∧ (∀ (x y : H) (α : 𝕜), φ (α • x, y) = star_ring_end 𝕜 α * φ (x, y))

/-- A linear functional $f$ on $M_n$ is positive and faithful if and only if $(x,y)\mapsto f(x^*y)$ defines an inner product on $M_n$. -/
lemma module.dual.is_faithful_pos_map_iff_is_inner_of_matrix (φ : module.dual ℂ (matrix n n ℂ)) :
  φ.is_faithful_pos_map
    ↔ is_inner (λ xy : matrix n n ℂ × matrix n n ℂ, φ (xy.1ᴴ ⬝ xy.2)) :=
begin
  let ip := λ xy : matrix n n ℂ × matrix n n ℂ, φ (xy.1ᴴ ⬝ xy.2),
  have hip : ∀ x y, ip (x, y) = φ (xᴴ ⬝ y) := λ x y, rfl,
  have Hip : (∀ x y z, ip (x+y, z) = ip (x, z) + ip (y, z)) ∧
    (∀ (x y) (α : ℂ), ip (α • x, y) = star_ring_end ℂ α * ip (x, y)),
  { simp only [ip],
    simp_rw [conj_transpose_add, matrix.add_mul, map_add, conj_transpose_smul, matrix.smul_mul,
      smul_hom_class.map_smul, complex.star_def, smul_eq_mul, eq_self_iff_true, forall_3_true_iff,
      true_and], },
  simp_rw [is_inner, ← hip, Hip, eq_self_iff_true, forall_3_true_iff, true_and, and_true],
  split,
  { intros h,
    simp_rw [hip, ← h.1.is_real _, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose],
    have := λ x, h.1 x,
    simp only [is_R_or_C.nonneg_def'] at this,
    exact ⟨λ x y, rfl, ⟨λ x, (this x).2, h.2⟩⟩, },
  { intros h,
    refine ⟨_, h.2.2⟩,
    simp_rw [module.dual.is_pos_map, star_eq_conj_transpose, mul_eq_mul, ← hip,
      is_R_or_C.nonneg_def', is_R_or_C.re_eq_complex_re,
      ← complex.conj_eq_iff_re, star_ring_end_apply, ← h.1, eq_self_iff_true, true_and],
    exact h.2.1, },
end

theorem module.dual.is_faithful_pos_map_of_matrix_tfae (φ : module.dual ℂ (matrix n n ℂ)) :
  tfae [φ.is_faithful_pos_map,
    φ.matrix.pos_def,
    is_inner (λ xy : matrix n n ℂ × matrix n n ℂ, φ (xy.1ᴴ ⬝ xy.2))] :=
begin
  tfae_have : 1 ↔ 2,
  { exact φ.is_faithful_pos_map_iff_of_matrix, },
  tfae_have : 1 ↔ 3,
  { exact φ.is_faithful_pos_map_iff_is_inner_of_matrix, },
  tfae_finish,
end

@[instance, reducible] noncomputable def module.dual.is_faithful_pos_map.normed_add_comm_group
  {φ : module.dual ℂ (matrix n n ℂ)} [hφ : fact φ.is_faithful_pos_map] :
  normed_add_comm_group (matrix n n ℂ) :=
begin
  have := φ.is_faithful_pos_map_iff_is_inner_of_matrix.mp hφ.elim,
  exact @inner_product_space.core.to_normed_add_comm_group ℂ (matrix n n ℂ) _ _ _
  { inner := λ x y, φ (xᴴ ⬝ y),
    conj_symm := λ x y, (this.1 _ _).symm,
    nonneg_re := λ x, (this.2.1 _),
    definite := λ x hx, (this.2.2.1 _).mp hx,
    add_left := λ x y z, this.2.2.2.1 _ _ _,
    smul_left := λ x y r, this.2.2.2.2 _ _ _ },
end

@[instance, reducible] noncomputable def module.dual.is_faithful_pos_map.inner_product_space
  {φ : module.dual ℂ (matrix n n ℂ)} [hφ : fact φ.is_faithful_pos_map] :
  inner_product_space ℂ (matrix n n ℂ) :=
inner_product_space.of_core _

@[instance, reducible] noncomputable def module.dual.pi.normed_add_comm_group
  {k : Type*} [fintype k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {φ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)} [hφ : (Π i, fact (φ i).is_faithful_pos_map)] :
  normed_add_comm_group (Π i, matrix (s i) (s i) ℂ) :=
begin
  exact @inner_product_space.core.to_normed_add_comm_group ℂ (Π i, matrix (s i) (s i) ℂ) _ _ _
  { inner := λ x y, ∑ i, (inner (x i) (y i)),
    conj_symm := λ x y, by { simp only [inner, map_sum, inner_conj_symm], },
    nonneg_re := λ x, by { simp only [inner, map_sum],
      apply finset.sum_nonneg,
      intros i hi,
      exact inner_self_nonneg, },
    definite := λ x hx, by { simp_rw [inner] at hx,
      rw [finset.sum_eq_zero_iff_of_nonneg] at hx,
      simp_rw [finset.mem_univ, true_implies_iff, inner_self_eq_zero] at hx,
      ext1 i,
      exact hx i,
      { intros i hi,
        rw [is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re],
        exact ⟨inner_self_conj _, inner_self_nonneg⟩, }, },
    add_left := λ x y z, by { simp_rw [inner, pi.add_apply, inner_add_left, finset.sum_add_distrib], },
    smul_left := λ x y r, by { simp_rw [inner, pi.smul_apply, inner_smul_left,
      finset.mul_sum], } },
end

@[instance, reducible] noncomputable def module.dual.pi.inner_product_space
  {k : Type*} [fintype k]
  [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {φ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)} [hφ : Π i, fact (φ i).is_faithful_pos_map] :
  inner_product_space ℂ (Π i, matrix (s i) (s i) ℂ) :=
inner_product_space.of_core _


localized "attribute [instance] module.dual.is_faithful_pos_map.normed_add_comm_group" in functional
localized "attribute [instance] module.dual.is_faithful_pos_map.inner_product_space" in functional
localized "attribute [instance] module.dual.pi.normed_add_comm_group" in functional
localized "attribute [instance] module.dual.pi.inner_product_space" in functional
