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
- `linear_map.linear_functional_eq`
- `linear_map.is_pos_map_iff`
- `linear_map.is_faithful_pos_map_iff`
- `linear_map.is_tracial_faithful_pos_map_iff`
- `linear_map.is_faithful_pos_map_iff_is_inner`

-/

variables {𝕜 R n : Type*} [is_R_or_C 𝕜] [comm_semiring R] [fintype n] [decidable_eq n]

open_locale matrix big_operators
open matrix

/-- the matrix of a linear map `φ : M_n →ₗ[R] R` is given by
  `∑ i j, std_basis_matrix j i (φ (std_basis_matrix i j 1))`. -/
def linear_map.matrix (φ : matrix n n R →ₗ[R] R) :=
∑ i j : n, matrix.std_basis_matrix j i (φ (matrix.std_basis_matrix i j 1))

/-- given any linear functional `φ : M_n →ₗ[R] R`, we get `φ a = (φ.matrix ⬝ a).trace`. -/
lemma linear_map.linear_functional_eq' (φ : matrix n n R →ₗ[R] R) (a : matrix n n R) :
  φ a = (φ.matrix ⬝ a).trace :=
begin
  simp_rw [linear_map.matrix, smul_std_basis_matrix' _ _ (φ _)],
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
def linear_map.direct_sum {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R) :
  (Π i, matrix (s i) (s i) R) →ₗ[R] R :=
{ to_fun := λ a, ∑ i : k, φ i (a i),
  map_add' := λ x y, by simp only [map_add, pi.add_apply, finset.sum_add_distrib],
  map_smul' := λ r x, by simp only [smul_hom_class.map_smul, pi.smul_apply,
    finset.smul_sum, ring_hom.id_apply], }

/-- for direct sums, we get `φ x = ∑ i, ((φ i).matrix ⬝ x i).trace` -/
lemma linear_map.direct_sum.linear_functional_eq {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R)
  (x : Π i, matrix (s i) (s i) R) :
  linear_map.direct_sum φ x = ∑ i, ((φ i).matrix ⬝ x i).trace :=
begin
  simp_rw [linear_map.direct_sum, linear_map.coe_mk, linear_map.linear_functional_eq'],
end

lemma linear_map.direct_sum.linear_functional_eq' {k : Type*} [fintype k]
  [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R) (x : Π i, matrix (s i) (s i) R) :
  linear_map.direct_sum φ x = ∑ i, (block_diagonal' (φ i).matrix.include_block ⬝ block_diagonal' x).trace :=
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
  ... = linear_map.direct_sum φ x : (linear_map.direct_sum.linear_functional_eq _ _).symm,
end

/-- Any linear functional $f$ on $M_n$ is given by a unique matrix $Q \in M_n$ such that $f(x)=\operatorname{Tr}(Qx)$ for any $x \in M_n$. -/
lemma linear_map.linear_functional_eq (φ : matrix n n R →ₗ[R] R) :
  ∃! Q : matrix n n R, ∀ a : matrix n n R, φ a = (Q ⬝ a).trace :=
begin
  use φ.matrix,
  simp_rw [← linear_map.linear_functional_eq', eq_self_iff_true, forall_true_iff, true_and,
    linear_map.linear_functional_eq', ← matrix.ext_iff_trace, eq_comm,
    imp_self, forall_true_iff],
end

lemma linear_map.linear_functional_eq_of (φ : matrix n n R →ₗ[R] R) (x : matrix n n R)
  (h : ∀ a, φ a = (x ⬝ a).trace) :
  x = φ.matrix :=
begin
  simp_rw [linear_map.linear_functional_eq', ← matrix.ext_iff_trace] at h,
  exact h.symm,
end

def linear_map.direct_sum' {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R) :
  { x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal } →ₗ[R] R :=
begin
  let φ' := (linear_map.direct_sum φ) ∘ₗ matrix.block_diag'_linear_map,
  exact { to_fun := λ x, φ' ↑x,
    map_add' := λ x y, by { simp only [matrix.is_block_diagonal.coe_add, map_add], },
    map_smul' := λ x y, by { simp only [matrix.is_block_diagonal.coe_smul,
      smul_hom_class.map_smul, ring_hom.id_apply], } },
end

/-- `⨁_i φ_i ι_i (x_i) = φ_i (x_i)` -/
lemma linear_map.direct_sum_apply_single_block {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (φ : Π i, matrix (s i) (s i) R →ₗ[R] R) (x : Π i, matrix (s i) (s i) R)
  (i : k) :
  (linear_map.direct_sum φ) (include_block (x i)) = φ i (x i) :=
begin
  simp_rw [linear_map.direct_sum.linear_functional_eq, include_block_apply,
    ←mul_eq_mul, mul_dite, mul_zero, trace_iff, dite_apply, pi.zero_apply,
    finset.sum_dite_irrel, finset.sum_const_zero, finset.sum_dite_eq,
    finset.mem_univ, if_true, linear_map.linear_functional_eq', trace_iff],
  refl,
end

open_locale complex_order
open_locale direct_sum
/-- A linear functional $φ$ on $M_n$ is positive if $0 ≤ φ (x^*x)$ for all $x \in M_n$. -/
def linear_map.is_pos_map {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : A →ₗ[𝕜] 𝕜) : Prop :=
∀ a : A, 0 ≤ φ (star a * a)

/-- A linear functional $φ$ on $M_n$ is unital if $φ(1) = 1$. -/
def linear_map.is_unital {A : Type*} [add_comm_monoid A] [module R A] [has_one A]
  (φ : A →ₗ[R] R) : Prop :=
φ (1 : A) = 1

/-- A linear functional is called a state if it is positive and unital -/
def linear_map.is_state {A : Type*} [semiring A] [star_ring A] [module 𝕜 A] (φ : A →ₗ[𝕜] 𝕜) :
  Prop :=
φ.is_pos_map ∧ φ.is_unital

lemma linear_map.is_pos_map_of_matrix (φ : matrix n n 𝕜 →ₗ[𝕜] 𝕜) :
  φ.is_pos_map ↔ (∀ a : matrix n n 𝕜, a.pos_semidef → 0 ≤ φ a) :=
begin
  simp_rw [pos_semidef_iff, exists_imp_distrib],
  refine ⟨λ h, _, λ h, _⟩,
  { rintros a x rfl,
    exact h _, },
  { intros x,
    exact h _ _ rfl, },
end

/-- A linear functional $f$ on $M_n$ is said to be faithful if $f(x^*x)=0$ if and only if $x=0$ for any $x \in M_n$. -/
def linear_map.is_faithful {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : A →ₗ[𝕜] 𝕜) : Prop :=
∀ a : A, φ (star a * a) = 0 ↔ a = 0

lemma linear_map.is_faithful_of_matrix (φ : matrix n n 𝕜 →ₗ[𝕜] 𝕜) :
  φ.is_faithful ↔ (∀ a : matrix n n 𝕜, a.pos_semidef → (φ a = 0 ↔ a = 0)) :=
begin
  simp_rw [pos_semidef_iff, exists_imp_distrib],
  split,
  { rintros h' a x rfl,
    rw matrix.conj_transpose_mul_self_eq_zero,
    exact h' _, },
  { intros h' x,
    rw ← x.conj_transpose_mul_self_eq_zero,
    exact h' _ _ rfl, },
end

/-- A linear functional $f$ is positive if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$.  -/
lemma linear_map.is_pos_map_iff_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  φ.is_pos_map ↔ φ.matrix.pos_semidef :=
begin
  split,
  { intros hs,
    rw [linear_map.is_pos_map_of_matrix] at hs,
    simp only [linear_map.linear_functional_eq'] at hs,
    have thiseq : ∀ y, star y ⬝ᵥ φ.matrix.mul_vec y = (φ.matrix ⬝ vec_mul_vec y (star y)).trace,
    { intros y,
      rw [vec_mul_vec_eq, trace_mul_cycle', ← col_mul_vec],
      simp_rw [matrix.trace_iff', row_mul_col_apply, fintype.univ_punit,
        finset.sum_const, finset.card_singleton, nsmul_eq_mul, algebra_map.coe_one, one_mul], },
      rw pos_semidef.complex,
      intros y,
      rw [thiseq, ← is_R_or_C.re_to_complex, ← is_R_or_C.nonneg_def'],
      refine hs _ _,
      exact vec_mul_vec.pos_semidef _, },
  { intros hy y,
    rw [φ.linear_functional_eq', mul_eq_mul, ← matrix.mul_assoc, is_R_or_C.nonneg_def'],
    exact hy.trace_conj_transpose_mul_self_nonneg _, },
end

/-- A linear functional $f$ is a state if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such that its trace equals $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma linear_map.is_state_iff_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  φ.is_state ↔ φ.matrix.pos_semidef ∧ φ.matrix.trace = 1 :=
begin
  rw [linear_map.is_state, linear_map.is_pos_map_iff_of_matrix],
  refine ⟨λ h, ⟨h.1, _⟩, λ h, ⟨h.1, _⟩⟩,
  { rw [linear_map.is_unital, linear_map.linear_functional_eq', matrix.mul_one] at h,
    exact h.2, },
  { rw [linear_map.is_unital, linear_map.linear_functional_eq', matrix.mul_one],
    exact h.2, },
end

/-- A positive linear functional $f$ is faithful if and only if there exists a positive definite matrix such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma linear_map.is_pos_map.is_faithful_iff_of_matrix
  {φ : matrix n n ℂ →ₗ[ℂ] ℂ} (hs : φ.is_pos_map) :
  φ.is_faithful ↔ φ.matrix.pos_def :=
begin
  have hs' := hs,
  rw [linear_map.is_pos_map_of_matrix] at hs',
  rw linear_map.is_faithful_of_matrix,
  split,
  { rw linear_map.is_pos_map_iff_of_matrix at hs,
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
      { rw ← linear_map.linear_functional_eq',
        exact (is_R_or_C.pos_def.mp this32).1, }, }, },
  { intros hQ a ha,
    refine ⟨λ h, _, λ h, by rw [h, map_zero]⟩,
    obtain ⟨b, rfl⟩ := (pos_semidef_iff _).mp ha,
    rw [linear_map.linear_functional_eq', ← matrix.mul_assoc,
      nontracial.trace_conj_transpose_mul_self_eq_zero hQ] at h,
    rw [h, matrix.mul_zero], },
end

def linear_map.is_faithful_pos_map {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : A →ₗ[𝕜] 𝕜) : Prop :=
φ.is_pos_map ∧ φ.is_faithful

/-- A linear functional $φ$ is a faithful and positive if and only if there exists a unique positive definite matrix $Q$ such that $φ(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
lemma linear_map.is_faithful_pos_map_iff_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  φ.is_faithful_pos_map ↔ φ.matrix.pos_def :=
begin
  refine ⟨λ h, h.1.is_faithful_iff_of_matrix.mp h.2, _⟩,
  intros hQ,
  simp_rw [linear_map.is_faithful_pos_map, linear_map.is_faithful,
    linear_map.is_pos_map_iff_of_matrix, hQ.pos_semidef, true_and,
    linear_map.linear_functional_eq', mul_eq_mul, star_eq_conj_transpose, ← matrix.mul_assoc,
    nontracial.trace_conj_transpose_mul_self_eq_zero hQ, iff_self, forall_const],
end

/-- A state is faithful $f$ if and only if there exists a unique positive definite matrix $Q\in M_n$ with trace equal to $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x \in M_n$. -/
lemma linear_map.is_state.is_faithful_iff_of_matrix {φ : matrix n n ℂ →ₗ[ℂ] ℂ}
  (hs : φ.is_state) :
  φ.is_faithful ↔ φ.matrix.pos_def ∧ φ.matrix.trace = 1 :=
begin
  rw hs.1.is_faithful_iff_of_matrix,
  refine ⟨λ hQ, ⟨hQ,_⟩, λ hQ, hQ.1⟩,
  { rw [linear_map.is_state_iff_of_matrix] at hs,
    exact hs.2, },
end

lemma linear_map.is_faithful_state_iff_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  (φ.is_state ∧ φ.is_faithful)
    ↔ φ.matrix.pos_def ∧ φ.matrix.trace = 1 :=
begin
  refine ⟨λ h, h.1.is_faithful_iff_of_matrix.mp h.2, _⟩,
  intros hQ,
  simp_rw [linear_map.is_faithful, linear_map.is_state_iff_of_matrix, hQ.2, hQ.1.pos_semidef,
    eq_self_iff_true, true_and],
  rw ← linear_map.is_faithful_pos_map_iff_of_matrix at hQ,
  exact hQ.1.2,
end

/-- A linear functional $f$ is tracial if and only if $f(xy)=f(yx)$ for all $x,y$. -/
def linear_map.is_tracial  {A : Type*} [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] (φ : A →ₗ[𝕜] 𝕜) :
  Prop :=
∀ x y : A, φ (x * y) = φ (y * x)

/-- A linear functional is tracial and positive if and only if there exists a non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
lemma linear_map.is_tracial_pos_map_iff_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  (φ.is_pos_map ∧ φ.is_tracial) ↔ ∃ α : nnreal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
begin
  split,
  { simp_rw [linear_map.is_pos_map_iff_of_matrix],
    rintros ⟨hQ, h2⟩,
    simp_rw [linear_map.is_tracial, linear_map.linear_functional_eq',
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
    have : 0 ≤ is_R_or_C.re (Q i i),
    { rw pos_semidef.complex at hQ,
      specialize hQ (λ j, ite (i = j) 1 0),
      simp_rw [dot_product, mul_vec, dot_product, pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at hQ,
      exact hQ.2, },
    let α : nnreal := ⟨is_R_or_C.re (Q i i), this⟩,
    have hα : (α : ℂ) = is_R_or_C.re (Q i i) := rfl,
    have hα' : is_R_or_C.re (Q i i) = α := rfl,
    refine ⟨α, _⟩,
    { simp only [smul_eq_diagonal_mul, ← hα', matrix.mul_one],
      rw ← this',
      exact HH, }, },
  { rintros ⟨α, hα1⟩,
    simp_rw [linear_map.is_pos_map, linear_map.is_tracial, linear_map.linear_functional_eq',
      hα1, is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply, matrix.smul_mul, matrix.one_mul, trace_star, conj_transpose_smul,
      mul_eq_mul, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose, is_R_or_C.star_def, is_R_or_C.conj_of_real,
      trace_smul, smul_eq_mul, is_R_or_C.of_real_mul_re, mul_nonneg (nnreal.coe_nonneg _)
        (trace_conj_transpose_mul_self_re_nonneg _), and_true],
    exact ⟨λ _, rfl, λ _ _, by rw trace_mul_comm⟩, },
end


/-- A linear functional is tracial and positive if and only if there exists a unique non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
lemma linear_map.is_tracial_pos_map_iff'_of_matrix [nonempty n] (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  (φ.is_pos_map ∧ φ.is_tracial) ↔ ∃! α : nnreal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
begin
  split,
  { simp_rw [linear_map.is_pos_map_iff_of_matrix],
    rintros ⟨hQ, h2⟩,
    simp_rw [linear_map.is_tracial, linear_map.linear_functional_eq',
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
    have : 0 ≤ is_R_or_C.re (Q i i),
    { rw pos_semidef.complex at hQ,
      specialize hQ (λ j, ite (i = j) 1 0),
      simp_rw [dot_product, mul_vec, dot_product, pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] at hQ,
      exact hQ.2, },
    let α : nnreal := ⟨is_R_or_C.re (Q i i), this⟩,
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
    simp_rw [linear_map.is_pos_map, linear_map.is_tracial, linear_map.linear_functional_eq',
      hα1, is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply, matrix.smul_mul, matrix.one_mul, trace_star, conj_transpose_smul,
      mul_eq_mul, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose, is_R_or_C.star_def, is_R_or_C.conj_of_real,
      trace_smul, smul_eq_mul, is_R_or_C.of_real_mul_re, mul_nonneg (nnreal.coe_nonneg _)
        (trace_conj_transpose_mul_self_re_nonneg _), and_true],
    exact ⟨λ _, rfl, λ _ _, by rw trace_mul_comm⟩, },
end

/-- A linear functional $f$ is tracial positive and faithful if and only if there exists a positive real number $\alpha$ such that $f\colon x\mapsto \alpha \operatorname{Tr}(x)$. -/
lemma linear_map.is_tracial_faithful_pos_map_iff_of_matrix [nonempty n] (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
  (φ.is_faithful_pos_map ∧ φ.is_tracial)
    ↔ ∃! α : {x : nnreal // 0 < x}, φ.matrix = (((α : nnreal) : ℝ) : ℂ) • 1 :=
begin
  rw [linear_map.is_faithful_pos_map, and_comm φ.is_pos_map _, and_assoc,
    linear_map.is_tracial_pos_map_iff'_of_matrix],
  split,
  { rintros ⟨h1, ⟨α, hα, h⟩⟩,
    have : 0 < (α : ℝ) :=
    by { rw [nnreal.coe_pos, pos_iff_ne_zero],
      intros HH,
      rw linear_map.is_faithful at h1,
      specialize h1 ((1 : matrix n n ℂ)ᴴ ⬝ (1 : matrix n n ℂ)),
      simp only [matrix.conj_transpose_one, matrix.one_mul, matrix.mul_one,
        linear_map.linear_functional_eq', mul_eq_mul, star_eq_conj_transpose] at h1,
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
    { simp_rw [linear_map.is_faithful, linear_map.linear_functional_eq', h1,
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

lemma linear_map.is_pos_map.is_real {φ : matrix n n ℂ →ₗ[ℂ] ℂ}
  (hφ : φ.is_pos_map) :
  φ.is_real :=
begin
  intros x,
  rw linear_map.is_pos_map_iff_of_matrix at hφ,
  simp_rw [linear_map.linear_functional_eq', trace_star, conj_transpose_mul, hφ.1.eq],
  rw [trace_mul_comm],
  refl,
end

lemma linear_map.is_pos_map.direct_sum.is_real {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {ψ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ} (hψ : Π i, (ψ i).is_pos_map) :
  (linear_map.direct_sum ψ).is_real :=
begin
  intros x,
  rw [matrix_eq_sum_include_block x],
  simp only [map_sum, star_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  simp only [← linear_map.is_pos_map.is_real (hψ i) (x i), include_block_conj_transpose,
    linear_map.direct_sum_apply_single_block],
  refl,
end

/-- A function $H \times H \to 𝕜$ defines an inner product if it satisfies the following. -/
def is_inner {H : Type*} [add_comm_monoid H] [module 𝕜 H] (φ : H×H → 𝕜) : Prop :=
(∀ x y : H, φ (x, y) = star (φ (y, x))) ∧ (∀ x : H, 0 ≤ is_R_or_C.re (φ (x, x))) ∧
  (∀ x : H, φ (x, x) = 0 ↔ x = 0) ∧ (∀ x y z : H, φ (x+y, z) = φ (x, z) + φ (y, z)) ∧
    (∀ (x y : H) (α : 𝕜), φ (α • x, y) = star_ring_end 𝕜 α * φ (x, y))

/-- A linear functional $f$ on $M_n$ is positive and faithful if and only if $(x,y)\mapsto f(x^*y)$ defines an inner product on $M_n$. -/
lemma linear_map.is_faithful_pos_map_iff_is_inner_of_matrix (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
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
    simp_rw [linear_map.is_pos_map, star_eq_conj_transpose, mul_eq_mul, ← hip,
      is_R_or_C.nonneg_def', is_R_or_C.re_eq_complex_re,
      ← complex.conj_eq_iff_re, star_ring_end_apply, ← h.1, eq_self_iff_true, true_and],
    exact h.2.1, },
end

theorem linear_map.is_faithful_pos_map_of_matrix_tfae (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
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

@[instance, reducible] noncomputable def linear_map.is_faithful_pos_map.normed_add_comm_group
  {φ : matrix n n ℂ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map] :
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

@[instance, reducible] noncomputable def linear_map.is_faithful_pos_map.inner_product_space
  {φ : matrix n n ℂ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map] :
  inner_product_space ℂ (matrix n n ℂ) :=
inner_product_space.of_core _

@[instance, reducible] noncomputable def linear_map.direct_sum.normed_add_comm_group
  {k : Type*} [fintype k]
  [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {φ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ} [hφ : (Π i, fact (φ i).is_faithful_pos_map)] :
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

@[instance, reducible] noncomputable def linear_map.direct_sum.inner_product_space
  {k : Type*} [fintype k]
  [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {φ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map] :
  inner_product_space ℂ (Π i, matrix (s i) (s i) ℂ) :=
inner_product_space.of_core _


localized "attribute [instance] linear_map.is_faithful_pos_map.normed_add_comm_group" in functional
localized "attribute [instance] linear_map.is_faithful_pos_map.inner_product_space" in functional
localized "attribute [instance] linear_map.direct_sum.normed_add_comm_group" in functional
localized "attribute [instance] linear_map.direct_sum.inner_product_space" in functional
