/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.nontracial
import quantum_graph.iso
import linear_algebra.to_matrix_of_equiv
import linear_algebra.my_ips.mat_ips
import quantum_graph.qam_A
import linear_algebra.my_matrix.spectra

section

/-!

# Examples of single-edged quantum graph

This file contains examples of single-edged quantum graphs over `M₂(ℂ)`. The main result is that all single-edged quantum graphs over `M₂(ℂ)` are isomorphic each other.

-/

open matrix

open_locale matrix kronecker functional

variables {n : Type*} [fintype n] [decidable_eq n]

local notation `ℍ` := matrix n n ℂ

def trace_module_dual {𝕜 n : Type*} [fintype n] [is_R_or_C 𝕜] :
  module.dual 𝕜 (matrix n n 𝕜) :=
trace_linear_map n 𝕜 𝕜

@[instance] def trace_is_faithful_pos_map
  {n : Type*} [fintype n] {𝕜 : Type*} [is_R_or_C 𝕜] :
  fact (trace_module_dual : module.dual 𝕜 (matrix n n 𝕜)).is_faithful_pos_map :=
begin
  apply fact.mk,
  simp_rw [module.dual.is_faithful_pos_map, module.dual.is_faithful, module.dual.is_pos_map,
    trace_module_dual, trace_linear_map_apply, is_R_or_C.nonneg_def', ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply,
    trace_star, mul_eq_mul, star_eq_conj_transpose, conj_transpose_mul,
    conj_transpose_conj_transpose, trace_conj_transpose_mul_self_eq_zero,
    trace_conj_transpose_mul_self_re_nonneg, eq_self_iff_true, iff_self,
    implies_true_iff, and_true, forall_true_iff],
end

lemma trace_module_dual_matrix {n : Type*}
  [fintype n] [decidable_eq n] :
  (trace_module_dual : module.dual ℂ (matrix n n ℂ)).matrix = 1 :=
begin
  ext1,
  have := (trace_module_dual : module.dual ℂ (matrix n n ℂ)).apply
    (λ k l, ite (j = k) (ite (i = l) 1 0) 0),
  simp only [trace_module_dual, trace_linear_map_apply, trace_iff, mul_apply, mul_ite, mul_zero, mul_one,
    finset.sum_ite_eq, finset.mem_univ, if_true] at this,
  rw [trace_module_dual, ← this],
  refl,
end

open_locale big_operators
lemma pos_def_one_rpow (n : Type*) [fintype n] [decidable_eq n] (r : ℝ) :
  (pos_def_one : pos_def (1 : matrix n n ℂ)).rpow r = 1 :=
begin
  rw [pos_def.rpow, inner_aut_eq_iff, inner_aut_apply_one,
    ← coe_diagonal_eq_diagonal_coe],
  nth_rewrite_rhs 0 ← diagonal_one,
  rw [diagonal_eq_diagonal_iff],
  intros i,
  simp_rw [function.comp_apply, pi.pow_apply],
  rw [← is_R_or_C.of_real_one, is_R_or_C.of_real_inj, is_hermitian.eigenvalues_eq,
    one_mul_vec],
  simp_rw [dot_product, pi.star_apply, transpose_apply, ← conj_transpose_apply,
    ← is_hermitian.conj_transpose_eigenvector_matrix_inv, ← mul_apply,
    ← is_hermitian.conj_transpose_eigenvector_matrix, conj_transpose_conj_transpose,
    ← star_eq_conj_transpose, ← mul_eq_mul,
    mem_unitary_group_iff'.mp (is_hermitian.eigenvector_matrix_mem_unitary_group _), one_apply_eq, is_R_or_C.one_re],
  exact real.one_rpow _,
end

private lemma pos_def_one_rpow_eq_trace_matrix_rpow
  (r : ℝ) :
  (pos_def_one : pos_def (1 : matrix n n ℂ)).rpow r
    = (trace_is_faithful_pos_map.elim : (trace_module_dual : module.dual ℂ ℍ).is_faithful_pos_map).matrix_is_pos_def.rpow r :=
begin
  rw [eq_comm, pos_def_one_rpow, pos_def.rpow, inner_aut_eq_iff,
    inner_aut_apply_one, ← coe_diagonal_eq_diagonal_coe],
  nth_rewrite_rhs 0 ← diagonal_one,
  rw [diagonal_eq_diagonal_iff],
  intros i,
  simp_rw [function.comp_apply, pi.pow_apply],
  rw [← is_R_or_C.of_real_one, is_R_or_C.of_real_inj, is_hermitian.eigenvalues_eq],
  simp_rw [trace_module_dual_matrix, one_mul_vec, dot_product, pi.star_apply,
    transpose_apply, ← conj_transpose_apply,
    ← is_hermitian.conj_transpose_eigenvector_matrix_inv, ← mul_apply,
    ← is_hermitian.conj_transpose_eigenvector_matrix, conj_transpose_conj_transpose,
    ← star_eq_conj_transpose, ← mul_eq_mul,
    mem_unitary_group_iff'.mp (is_hermitian.eigenvector_matrix_mem_unitary_group _), one_apply_eq, is_R_or_C.one_re],
  exact real.one_rpow _,
end

private lemma aux.ug :
  (trace_is_faithful_pos_map.elim
    : (trace_module_dual : module.dual ℂ ℍ).is_faithful_pos_map).to_matrix.symm
    = to_lin_of_alg_equiv :=
by { ext1,
  letI := fact.mk (@trace_is_faithful_pos_map n _ ℂ _),
  simp_rw [module.dual.is_faithful_pos_map.to_matrix_symm_apply],
  simp_rw [to_lin_of_alg_equiv_eq, rank_one_std_basis, one_smul, linear_map.ext_iff,
    linear_map.sum_apply, linear_map.smul_apply, linear_map.coe_mk,
    continuous_linear_map.coe_coe, rank_one_apply, module.dual.is_faithful_pos_map.inner_coord',
    ← pos_def_one_rpow_eq_trace_matrix_rpow, pos_def_one_rpow, matrix.mul_one,
    smul_std_basis_matrix, smul_eq_mul, module.dual.is_faithful_pos_map.basis_apply,
    trace_module_dual_matrix, pos_def_one_rpow, matrix.mul_one, smul_std_basis_matrix, smul_eq_mul, mul_one],
  intros x,
  repeat { nth_rewrite_lhs 0 ← finset.sum_product',
    simp_rw [prod.mk.eta],
    apply finset.sum_congr rfl,
    intros _ _, },
  refl, }

lemma matrix.std_basis_matrix.transpose {R n m : Type*} [decidable_eq n] [decidable_eq m]
  [semiring R] (i : n) (j : m) :
  (std_basis_matrix i j (1 : R))ᵀ = std_basis_matrix j i (1 : R) :=
begin
  ext1,
  simp_rw [transpose_apply, std_basis_matrix, and_comm],
end

section move

/-- obviously, `n × unit → R` is linearly equiv to `n → R` -/
def pi_prod_unit_equiv_pi {R n : Type*} [semiring R] :
  ((n × unit) → R) ≃ₗ[R] n → R :=
{ to_fun := λ x i, x (i, punit.star),
  inv_fun := λ x i, x i.1,
  left_inv := λ x, by { ext1, simp_rw [col_apply],
    have : punit.star = x_1.2,
    { simp only [eq_iff_true_of_subsingleton], },
    rw [this, prod.mk.eta], },
  right_inv := λ x, by { ext1, simp only [col_apply], },
  map_add' := λ x y, by { simp only [pi.add_apply], refl, },
  map_smul' := λ r x, by { simp only [pi.smul_apply, ring_hom.id_apply], refl, } }

/-- `matrix.col` written as a linear equivalence -/
def matrix.of_col {R n : Type*} [semiring R] :
  matrix n unit R ≃ₗ[R] n → R :=
(reshape : matrix n unit R ≃ₗ[R] n × unit → R).trans pi_prod_unit_equiv_pi

/-- obviously, `matrix n (m × unit)` is linearly equivalent to `matrix n m R` -/
def matrix_prod_unit_right {R n m : Type*} [semiring R] :
  matrix n (m × unit) R ≃ₗ[R] matrix n m R :=
{ to_fun := λ x i j, x i (j, punit.star),
  inv_fun := λ x i j, x i j.1,
  left_inv := λ x, by { ext1, simp_rw [col_apply],
    have : (j.1, punit.star) = j,
    { rw [← @prod.mk.eta _ _ j],
      ext,
      simp only [eq_iff_true_of_subsingleton], },
    rw this, },
  right_inv := λ x, by { ext1, simp only [col_apply], },
  map_add' := λ x y, by { simp only [pi.add_apply], refl, },
  map_smul' := λ r x, by { simp only [pi.smul_apply, ring_hom.id_apply], refl, } }

/-- `vec_mul_vec (reshape x) (star (reshape y))` written as a kronecker product of their
  corresponding vectors (via `reshape`). -/
lemma col_mul_col_conj_transpose_is_kronecker_of_vectors {R m n p q : Type*}
  [semiring R] [has_star R] (x : matrix m n R) (y : matrix p q R) :
  col (reshape x) ⬝ (col (reshape y))ᴴ
    = ((reshape : matrix _ _ R ≃ₗ[R] (_ × _) → R).symm
      (matrix.of_col (matrix_prod_unit_right ((col (reshape x)) ⊗ₖ (col (reshape yᴴᵀ)))))) :=
begin
  ext1,
  simp_rw [reshape_symm_apply, matrix.of_col, matrix_prod_unit_right, pi_prod_unit_equiv_pi,
    linear_equiv.trans_apply, linear_equiv.coe_mk, reshape_apply,
    kronecker_apply, col_apply, conj_transpose_col, ← vec_mul_vec_eq,
    vec_mul_vec_apply, pi.star_apply, reshape_apply, conj_apply],
end

end move

open_locale tensor_product

open_locale complex_conjugate

private lemma linear_map.rsmul_adjoint {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  (A : E →ₗ[𝕜] E) (r : ℝ) :
  ((r : 𝕜) • A).adjoint = (r : 𝕜) • A.adjoint :=
begin
  simp_rw [← @linear_map.star_eq_adjoint 𝕜 E, star_smul, is_R_or_C.star_def,
    is_R_or_C.conj_of_real],
end

/-- when a matrix $x$ is non-zero, then for any unitary $U$, we also have $f_U(x)$ is non-zero -/
private noncomputable def inner_aut_inv.of_ne_zero (U : unitary_group n ℂ)
  (x : {x : matrix n n ℂ // x ≠ 0}) : {x : matrix n n ℂ // x ≠ 0} :=
begin
  have : inner_aut U⁻¹ (x : matrix n n ℂ) ≠ 0 ↔ (x : ℍ) ≠ 0,
  { simp_rw [ne.def, inner_aut_eq_iff, inner_aut_apply_zero, iff_self], },
  exact (⟨inner_aut U⁻¹ x, (this.mpr (set.mem_set_of.mp (subtype.mem x)))⟩
    : {x : matrix n n ℂ // x ≠ 0}),
end

private lemma inner_aut_inv.of_ne_zero_eq (U : unitary_group n ℂ) (x : {x : ℍ // x ≠ 0}) :
  (inner_aut_inv.of_ne_zero U x : ℍ) = inner_aut U⁻¹ x :=
rfl

lemma star_alg_equiv.eq_comp_iff {R E₁ E₂ E₃ : Type*}
  [_inst_1 : comm_semiring R] [_inst_2 : semiring E₂] [_inst_3 : semiring E₃]
  [_inst_4 : add_comm_monoid E₁] [_inst_5 : algebra R E₂] [_inst_6 : algebra R E₃]
  [_inst_7 : module R E₁] [_inst_8 : has_star E₂] [_inst_9 : has_star E₃]
  (f : E₂ ≃⋆ₐ[R] E₃) (x : E₁ →ₗ[R] E₂) (y : E₁ →ₗ[R] E₃) :
  f.to_alg_equiv.to_linear_map.comp x = y
    ↔ x = f.symm.to_alg_equiv.to_linear_map.comp y :=
begin
  split; intros h,
  work_on_goal 1 { rw [←h], },
  work_on_goal 2 { rw [h], },
  all_goals { rw [linear_map.ext_iff],
    intros a,
    simp only [linear_map.comp_apply, star_alg_equiv.coe_to_alg_equiv,
      alg_equiv.to_linear_map_apply, star_alg_equiv.symm_apply_apply,
      star_alg_equiv.apply_symm_apply], },
end

lemma ite_comp {R U V W : Type*} [semiring R] [add_comm_monoid U] [add_comm_monoid V]
  [add_comm_monoid W]
  [module R U] [module R V] [module R W] {P : Prop} [decidable P]
  {x y : W →ₗ[R] U} {f : V →ₗ[R] W} :
  (ite P x y) ∘ₗ f = ite P (x ∘ₗ f) (y ∘ₗ f) :=
by split_ifs; simp
lemma comp_ite {R U V W : Type*} [semiring R] [add_comm_monoid U] [add_comm_monoid V]
  [add_comm_monoid W]
  [module R U] [module R V] [module R W] {P : Prop} [decidable P]
  {x y : W →ₗ[R] U} {f : U →ₗ[R] V} :
  f ∘ₗ (ite P x y) = ite P (f ∘ₗ x) (f ∘ₗ y) :=
by split_ifs; simp

lemma star_alg_equiv.comp_symm_self {R U V : Type*} [comm_semiring R]
  [semiring U] [semiring V] [algebra R U] [algebra R V] [has_star U] [has_star V]
  {f : U ≃⋆ₐ[R] V} :
  f.to_alg_equiv.to_linear_map.comp f.symm.to_alg_equiv.to_linear_map = 1 :=
begin
  rw [star_alg_equiv.eq_comp_iff, linear_map.comp_one],
end

lemma star_alg_equiv.symm_comp_self {R U V : Type*} [comm_semiring R]
  [semiring U] [semiring V] [algebra R U] [algebra R V] [has_star U] [has_star V]
  {f : U ≃⋆ₐ[R] V} :
  f.symm.to_alg_equiv.to_linear_map.comp f.to_alg_equiv.to_linear_map = 1 :=
begin
  simp only [linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply,
    star_alg_equiv.coe_to_alg_equiv, star_alg_equiv.symm_apply_apply, linear_map.one_apply,
    eq_self_iff_true, forall_true_iff],
end

lemma qam.iso_preserves_ir_reflexive [nontrivial n] {φ : module.dual ℂ ℍ}
  [hφ : fact φ.is_faithful_pos_map]
  {x y : ℍ →ₗ[ℂ] ℍ} (hxhy : @qam.iso n _ _ φ x y)
  (ir_reflexive : Prop) [decidable ir_reflexive] :
  qam.refl_idempotent hφ.elim x 1 = ite ir_reflexive 1 0
    ↔ qam.refl_idempotent hφ.elim y 1 = ite ir_reflexive 1 0 :=
begin
  obtain ⟨f, hf, h⟩ := hxhy,
  rw [star_alg_equiv.comp_eq_iff, linear_map.comp_assoc] at hf,
  rw [list.tfae.out (@module.dual.is_faithful_pos_map.star_alg_equiv_is_isometry_tfae n _ _ φ _ _ f) 0 4] at h,
  rw [hf, qam_ir_reflexive_star_alg_equiv_conj h, ← linear_map.comp_assoc, star_alg_equiv.comp_eq_iff,
    star_alg_equiv.symm_symm, star_alg_equiv.eq_comp_iff],
  simp only [ite_comp, comp_ite, linear_map.zero_comp, linear_map.one_comp,
    linear_map.comp_zero, linear_map.comp_one, star_alg_equiv.symm_comp_self,
    iff_self],
end

/-- a function `f : A → B` is _almost injective_ if for all $x, y \in A$,
  if $f(x)=f(y)$ then there exists some $0\neq\alpha \in \mathbb{C}$ such that
  $x = \alpha y$ (in other words, $x$ and $y$ are co-linear) -/
def function.is_almost_injective {A B : Type*} (f : A → B) [has_smul ℂˣ A] : Prop :=
∀ x y : A, f x = f y ↔ ∃ α : ℂˣ, x = α • y


open_locale big_operators complex_conjugate

private lemma nontracial_basis_apply {Q : ℍ} (hQ : Q.pos_def) (i j k l : n) :
  (std_basis_matrix i j 1 ⬝ hQ.rpow (-(1/2))) k l
    = ite (i = k) (hQ.rpow (-(1/2)) j l) 0 :=
begin
  simp_rw [mul_apply, std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
    finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true],
end

private lemma prod.eq' {α β : Type*} {p r : α} {q s : β} :
  (p,q) = (r,s) ↔ (p = r ∧ q = s) :=
prod.eq_iff_fst_eq_snd_eq

lemma matrix.is_almost_hermitian.spectrum {x : matrix n n ℂ} (hx : x.is_almost_hermitian) :
  spectrum ℂ x.to_lin' = {x_1 : ℂ | ∃ (i : n), hx.eigenvalues i = x_1} :=
begin
  nth_rewrite_lhs 0 matrix.is_almost_hermitian.eq_smul_matrix hx,
  nth_rewrite_lhs 0 hx.matrix_is_hermitian.spectral_theorem',
  simp_rw [← smul_hom_class.map_smul, inner_aut.spectrum_eq, ← diagonal_smul,
    diagonal.spectrum, pi.smul_apply, function.comp_apply, matrix.is_almost_hermitian.eigenvalues],
end

lemma matrix.is_hermitian.eigenvalues_eq_zero_iff
  {x : ℍ} (hx : x.is_hermitian) :
  coe ∘ hx.eigenvalues = (0 : n → ℂ) ↔ x = 0 :=
begin
  split,
  { intros h,
    rw [hx.spectral_theorem', h, pi.zero_def, diagonal_zero, map_zero], },
  { rintros rfl,
    ext1,
    simp only [function.comp_apply, hx.eigenvalues_eq, zero_mul_vec, dot_product_zero,
      map_zero, pi.zero_apply, complex.of_real_zero], },
end

private lemma matrix.is_almost_hermitian.matrix_is_hermitian.eigenvalues_ne_zero
  {x : {x : ℍ // x ≠ 0}} (hx : (x : ℍ).is_almost_hermitian) :
  (coe ∘ hx.matrix_is_hermitian.eigenvalues : n → ℂ) ≠ 0 :=
begin
  rw [ne.def, matrix.is_hermitian.eigenvalues_eq_zero_iff],
  have := hx.eq_smul_matrix,
  intros hh,
  rw [hh, smul_zero] at this,
  exact set.mem_set_of.mp (subtype.mem x) this,
end

private lemma example_aux {x : {x : matrix (fin 2) (fin 2) ℂ // x ≠ 0}}
  (hx : (x : matrix (fin 2) (fin 2) ℂ).is_almost_hermitian)
  (hh : (hx.matrix_is_hermitian.eigenvalues 0 : ℂ) = -((hx.matrix_is_hermitian.eigenvalues 1 : ℂ)))
  (i : fin 2) :
  (hx.matrix_is_hermitian.eigenvalues i : ℂ) ≠ 0 :=
begin
  have h := matrix.is_almost_hermitian.matrix_is_hermitian.eigenvalues_ne_zero hx,
  simp only [ne.def, function.funext_iff, function.comp_apply, pi.zero_apply] at h,
  revert i,
  simp_rw [fin.forall_fin_two, ne.def, hh, neg_eq_zero, and_self] at h ⊢,
  exact h,
end

lemma spectra_fin_two {x : matrix (fin 2) (fin 2) ℂ}
  (hx : (x : matrix (fin 2) (fin 2) ℂ).is_almost_hermitian) :
  hx.spectra = {(hx.eigenvalues 0 : ℂ), (hx.eigenvalues 1 : ℂ)} :=
rfl
lemma spectra_fin_two' {x : matrix (fin 2) (fin 2) ℂ}
  (hx : (x : matrix (fin 2) (fin 2) ℂ).is_almost_hermitian) :
  hx.spectra = [(hx.eigenvalues 0 : ℂ), (hx.eigenvalues 1 : ℂ)] :=
rfl
lemma spectra_fin_two'' {α : Type*} (a : fin 2 → α) :
  multiset.map (a : (fin 2) → α) finset.univ.val = {a 0, a 1} :=
rfl
lemma list.coe_inj {α : Type*} (l₁ l₂ : list α) :
  (l₁ : multiset α) = l₂ ↔ l₁ ~ l₂ :=
multiset.coe_eq_coe
lemma spectra_fin_two_ext_aux {A : Type*} (α β γ : A) :
  ({α, α} : multiset A) = {β, γ} ↔ α = β ∧ α = γ :=
begin
  simp only [multiset.insert_eq_cons],
  split,
  { intro h,
    simp_rw [multiset.cons_eq_cons, multiset.singleton_inj, multiset.singleton_eq_cons_iff] at h,
    rcases h with (h1 | ⟨h, cs, ⟨hcs₁, hcs₂⟩, ⟨hcs₃, hcs₄⟩⟩),
    { exact h1, },
    { exact ⟨hcs₁, hcs₃.symm⟩, }, },
  { rintro ⟨rfl, rfl⟩,
    refl, },
end
lemma spectra_fin_two_ext {α : Type*} (α₁ α₂ β₁ β₂ : α) :
  ({α₁, α₂} : multiset α) = {β₁, β₂} ↔
  ((α₁ = β₁ ∧ α₂ = β₂) ∨ (α₁ = β₂ ∧ α₂ = β₁)) :=
begin
  by_cases H₁ : α₁ = α₂,
  { rw [H₁, spectra_fin_two_ext_aux],
    split,
    { rintros ⟨h1, h2⟩,
      left,
      exact ⟨h1, h2⟩, },
    { rintros (⟨h1, h2⟩ | ⟨h1, h2⟩),
      { exact ⟨h1, h2⟩, },
      { exact ⟨h2, h1⟩, }, }, },
  by_cases h' : α₁ = β₁,
  { simp_rw [h', eq_self_iff_true, true_and, multiset.insert_eq_cons,
      multiset.cons_inj_right, multiset.singleton_inj],
    split,
    { intro hi,
      left,
      exact hi, },
    rintros (h | ⟨h1, h2⟩),
    { exact h, },
    { rw [← h', eq_comm] at h2,
      contradiction, }, },
  simp_rw [multiset.insert_eq_cons, multiset.cons_eq_cons,
    multiset.singleton_inj, multiset.singleton_eq_cons_iff, ne.def, h', false_and, false_or,
    not_false_iff, true_and],
  simp only [exists_eq_right_right, eq_self_iff_true, and_true, and.congr_right_iff,
    eq_comm, iff_self],
  simp_rw [and_comm, iff_self],
end
@[instance] def multiset.has_smul {α : Type*} [has_smul ℂ α] :
  has_smul ℂ (multiset α) :=
{ smul := λ a s, s.map ((•) a), }
lemma multiset.smul_fin_two {α : Type*} [has_smul ℂ α] (a b : α) (c : ℂ) :
  (c • ({a, b} : multiset α) : multiset α) = {c • a, c • b} :=
rfl
lemma is_almost_hermitian.smul_eq {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) (c : ℂ) :
  (hx.smul c).scalar • (hx.smul c).matrix = c • x := by
{ rw [← (hx.smul c).eq_smul_matrix], }

lemma spectra_fin_two_ext_of_traceless {α₁ α₂ β₁ β₂ : ℂ} (hα₂ : α₂ ≠ 0) (hβ₂ : β₂ ≠ 0)
  (h₁ : α₁ = - α₂) (h₂ : β₁ = - β₂) :
  ∃ c : ℂˣ, ({α₁, α₂} : multiset ℂ) = (c : ℂ) • {β₁, β₂} :=
begin
  simp_rw [h₁, h₂, multiset.smul_fin_two, smul_neg],
  refine ⟨units.mk0 (α₂ * β₂⁻¹) (mul_ne_zero hα₂ (inv_ne_zero hβ₂)), _⟩,
  simp_rw [units.coe_mk0, smul_eq_mul, mul_assoc, inv_mul_cancel hβ₂, mul_one],
end
lemma matrix.is_almost_hermitian.trace {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  x.trace = ∑ i, hx.eigenvalues i :=
begin
  simp_rw [is_almost_hermitian.eigenvalues, ← finset.smul_sum, ← is_hermitian.trace_eq,
    ← trace_smul],
  rw ← is_almost_hermitian.eq_smul_matrix hx,
end
noncomputable def matrix.is_almost_hermitian.eigenvector_matrix {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  matrix n n ℂ :=
hx.matrix_is_hermitian.eigenvector_matrix
lemma matrix.is_almost_hermitian.eigenvector_matrix_eq {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  hx.eigenvector_matrix = hx.matrix_is_hermitian.eigenvector_matrix :=
rfl
lemma matrix.is_almost_hermitian.eigenvector_matrix_mem_unitary_group {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  hx.eigenvector_matrix ∈ unitary_group n ℂ :=
hx.matrix_is_hermitian.eigenvector_matrix_mem_unitary_group
lemma matrix.is_almost_hermitian.spectral_theorem' {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  x = hx.scalar •
  (inner_aut ⟨hx.matrix_is_hermitian.eigenvector_matrix, is_hermitian.eigenvector_matrix_mem_unitary_group _⟩
    (diagonal (coe ∘ hx.matrix_is_hermitian.eigenvalues))) :=
begin
  rw [← is_hermitian.spectral_theorem', ← hx.eq_smul_matrix],
end
lemma matrix.is_almost_hermitian.eigenvalues_eq {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  hx.eigenvalues = hx.scalar • (coe ∘ hx.matrix_is_hermitian.eigenvalues : n → ℂ) :=
rfl
lemma matrix.is_almost_hermitian.spectral_theorem {x : matrix n n ℂ}
  (hx : x.is_almost_hermitian) :
  x = inner_aut ⟨hx.eigenvector_matrix, hx.eigenvector_matrix_mem_unitary_group⟩
    (diagonal hx.eigenvalues) :=
begin
  simp_rw [hx.eigenvalues_eq, diagonal_smul, smul_hom_class.map_smul, hx.eigenvector_matrix_eq],
  exact matrix.is_almost_hermitian.spectral_theorem' _,
end
lemma matrix.is_almost_hermitian.eigenvalues_eq_zero_iff
  {x : matrix n n ℂ} (hx : x.is_almost_hermitian) :
  hx.eigenvalues = 0 ↔ x = 0 :=
begin
  simp_rw [matrix.is_almost_hermitian.eigenvalues_eq, smul_eq_zero,
    matrix.is_hermitian.eigenvalues_eq_zero_iff, ← smul_eq_zero],
  rw [← hx.eq_smul_matrix],
  simp only [iff_self],
end
private lemma matrix.is_almost_hermitian.eigenvalues_eq_zero_iff_aux
  {x : matrix (fin 2) (fin 2) ℂ} (hx : x.is_almost_hermitian) :
  hx.eigenvalues 0 = 0 ∧ hx.eigenvalues 1 = 0 ↔ x = 0 :=
begin
  rw [← hx.eigenvalues_eq_zero_iff, function.funext_iff],
  simp_rw [fin.forall_fin_two, pi.zero_apply, iff_self],
end

lemma matrix.diagonal_eq_zero_iff {x : n → ℂ} :
  diagonal x = 0 ↔ x = 0 :=
begin
  simp_rw [← diagonal_zero, diagonal_eq_diagonal_iff, function.funext_iff,
    pi.zero_apply, iff_self],
end

theorem qam_A.fin_two_iso (x y : {x : matrix (fin 2) (fin 2) ℂ // x ≠ 0})
  (hx1 : _root_.is_self_adjoint (qam_A trace_is_faithful_pos_map.elim x))
  (hx2 : qam.refl_idempotent trace_is_faithful_pos_map.elim (qam_A trace_is_faithful_pos_map.elim x) 1 = 0)
  (hy1 : _root_.is_self_adjoint (qam_A trace_is_faithful_pos_map.elim y))
  (hy2 : qam.refl_idempotent trace_is_faithful_pos_map.elim (qam_A trace_is_faithful_pos_map.elim y) 1 = 0) :
  @qam.iso (fin 2) _ _ (trace_module_dual)
    (qam_A trace_is_faithful_pos_map.elim x)
    (qam_A trace_is_faithful_pos_map.elim y) :=
begin
  simp_rw [qam_A.iso_iff, trace_module_dual_matrix, commute.one_left,
    and_true, smul_hom_class.map_smul],
  rw exists_comm,
  obtain ⟨Hx, hxq⟩ := (qam_A.is_self_adjoint_iff x).mp hx1,
  obtain ⟨Hy, hyq⟩ := (qam_A.is_self_adjoint_iff y).mp hy1,
  simp_rw [qam_A.is_irreflexive_iff, Hx.trace, Hy.trace,
    fin.sum_univ_two, add_eq_zero_iff_eq_neg] at hx2 hy2,
  rw [matrix.is_almost_hermitian.spectral_theorem Hx,
    matrix.is_almost_hermitian.spectral_theorem Hy],
  have HX : diagonal Hx.eigenvalues = of ![![-Hx.eigenvalues 1, 0], ![0, Hx.eigenvalues 1]],
  { rw [← hx2, ← matrix.ext_iff],
    simp only [fin.forall_fin_two, diagonal_apply, of_apply, eq_self_iff_true, if_true,
      one_ne_zero, if_false, zero_ne_one, if_false],
    simp only [cons_val_zero, eq_self_iff_true, cons_val_one, head_cons, and_self], },
  have HY : diagonal Hy.eigenvalues = of ![![-Hy.eigenvalues 1, 0], ![0, Hy.eigenvalues 1]],
  { rw [← hy2, ← matrix.ext_iff],
    simp only [fin.forall_fin_two, diagonal_apply, of_apply, eq_self_iff_true, if_true,
      one_ne_zero, if_false, zero_ne_one, if_false],
    simp only [cons_val_zero, eq_self_iff_true, cons_val_one, head_cons, and_self], },
  simp_rw [HY, HX, inner_aut_apply_inner_aut],
  have hx₁ : Hx.eigenvalues 1 ≠ 0,
  { intros hx₁,
    have : diagonal Hx.eigenvalues = 0,
    { rw [HX, hx₁, neg_zero, ← matrix.ext_iff],
      simp_rw [fin.forall_fin_two],
      simp only [of_apply, pi.zero_apply],
      simp only [cons_val_zero, cons_val_one, head_cons, and_self], },
    rw [matrix.diagonal_eq_zero_iff, matrix.is_almost_hermitian.eigenvalues_eq_zero_iff] at this,
    exact (subtype.mem x) this, },
  have hy₁ : Hy.eigenvalues 1 ≠ 0,
  { intros hy₁,
    have : diagonal Hy.eigenvalues = 0,
    { rw [HY, hy₁, neg_zero, ← matrix.ext_iff],
      simp_rw [fin.forall_fin_two],
      simp only [of_apply, pi.zero_apply],
      simp only [cons_val_zero, cons_val_one, head_cons, and_self], },
    rw [matrix.diagonal_eq_zero_iff, matrix.is_almost_hermitian.eigenvalues_eq_zero_iff] at this,
    exact (subtype.mem y) this, },
  refine ⟨units.mk0 ((Hx.eigenvalues 1) * (Hy.eigenvalues 1)⁻¹)
    (mul_ne_zero hx₁ (inv_ne_zero hy₁)),
    ⟨Hx.eigenvector_matrix, Hx.eigenvector_matrix_mem_unitary_group⟩
      * ⟨Hy.eigenvector_matrix, Hy.eigenvector_matrix_mem_unitary_group⟩⁻¹, _⟩,
  have : (Hx.eigenvalues 1 * (Hy.eigenvalues 1)⁻¹) • diagonal Hy.eigenvalues = diagonal Hx.eigenvalues,
  { rw [HX, HY],
    simp only [smul_of, smul_cons, algebra.id.smul_eq_mul, mul_neg, mul_zero,
      smul_empty, embedding_like.apply_eq_iff_eq],
    simp only [inv_mul_cancel_right₀ hy₁], },
  simp_rw [inv_mul_cancel_right, units.coe_mk0, ← smul_hom_class.map_smul, ← HY, ← HX, this],
end

theorem qam.fin_two_iso_of_single_edge
  {A B : matrix (fin 2) (fin 2) ℂ →ₗ[ℂ] matrix (fin 2) (fin 2) ℂ}
  (hx0 : real_qam trace_is_faithful_pos_map.elim A)
  (hy0 : real_qam trace_is_faithful_pos_map.elim B)
  (hx : hx0.edges = 1) (hy : hy0.edges = 1)
  (hx1 : _root_.is_self_adjoint A)
  (hx2 : qam.refl_idempotent trace_is_faithful_pos_map.elim A 1 = 0)
  (hy1 : _root_.is_self_adjoint B)
  (hy2 : qam.refl_idempotent trace_is_faithful_pos_map.elim B 1 = 0) :
  @qam.iso (fin 2) _ _ (trace_module_dual) A B :=
begin
  rw [real_qam.edges_eq_one_iff] at hx hy,
  obtain ⟨x, rfl⟩ := hx,
  obtain ⟨y, rfl⟩ := hy,
  exact qam_A.fin_two_iso x y hx1 hx2 hy1 hy2,
end

end
