/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.matrix.block
import linear_algebra.matrix.trace
import data.matrix.basis
import preq.dite
import linear_algebra.matrix.hermitian
import linear_algebra.my_tensor_product

/-!

# Include block

 This file defines `matrix.include_block` which immitates `direct_sum.component_of` but for `pi` instead of `direct_sum` :TODO:

 The direct sum in these files are sort of misleading.

-/

namespace matrix

def block_diagonal'_alg_hom {o : Type*} {m' : o → Type*} {α : Type*}
  [fintype o] [decidable_eq o] [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α] :
  (Π (i : o), matrix (m' i) (m' i) α) →ₐ[α] matrix (Σ (i : o), m' i) (Σ (i : o), m' i) α :=
{ to_fun := λ a, block_diagonal' a,
  map_one' := block_diagonal'_one,
  map_mul' := λ a b, block_diagonal'_mul _ _,
  map_zero' := block_diagonal'_zero,
  map_add' := λ a b, block_diagonal'_add _ _,
  commutes' := λ a, by { simp_rw [algebra.algebra_map_eq_smul_one, block_diagonal'_smul,
    block_diagonal'_one], } }
lemma block_diagonal'_alg_hom_apply {o : Type*} {m' : o → Type*} {α : Type*}
  [fintype o] [decidable_eq o] [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α]
  (x : Π (i : o), matrix (m' i) (m' i) α) :
  matrix.block_diagonal'_alg_hom x = block_diagonal' x :=
rfl

def block_diag'_linear_map {o : Type*} {m' n' : o → Type*}
  {α : Type*} [semiring α] :
  matrix (Σ (i : o), m' i) (Σ (i : o), n' i) α →ₗ[α] Π (i : o), matrix (m' i) (n' i) α :=
{ to_fun := λ x, matrix.block_diag' x,
  map_add' := λ x y, block_diag'_add x y,
  map_smul' := λ r x, block_diag'_smul r x }
lemma block_diag'_linear_map_apply {o : Type*} {m' : o → Type*} {n' : o → Type*}
  {α : Type*} [semiring α] (x : matrix (Σ (i : o), m' i) (Σ (i : o), n' i) α) :
  matrix.block_diag'_linear_map x = block_diag' x :=
rfl

lemma block_diag'_linear_map_block_diagonal'_alg_hom
  {o : Type*} {m' : o → Type*} {α : Type*}
  [fintype o] [decidable_eq o] [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α]
  (x : Π (i : o), matrix (m' i) (m' i) α) :
  matrix.block_diag'_linear_map (matrix.block_diagonal'_alg_hom x) = x :=
block_diag'_block_diagonal' x

lemma block_diagonal'_ext {R : Type*} [semiring R]
  {k : Type*} [fintype k]
  [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (x y : matrix (Σ i, s i) (Σ i, s i) R) :
  x = y ↔ ∀ i j k l, x ⟨i,j⟩ ⟨k,l⟩ = y ⟨i,j⟩ ⟨k,l⟩ :=
by simp only [function.funext_iff, sigma.forall]

def is_block_diagonal
  {o : Type*} {m' : o → Type*} {α : Type*}
  [fintype o] [decidable_eq o] [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α]
  (x : matrix (Σ i, m' i) (Σ i, m' i) α) : Prop :=
block_diagonal' (block_diag' x) = x

def include_block {o : Type*} [fintype o] [decidable_eq o] {m' : o → Type*}
  {α : Type*}
  [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α]
  {i : o} :
  matrix (m' i) (m' i) α →ₗ[α] Π (j : o), matrix (m' j) (m' j) α :=
{ to_fun := λ x j, dite (i = j) (λ h, eq.mp (by rw [h]) x) (λ _, 0),
  map_add' := λ x y,
    by { ext,
    simp only [dite_apply, dite_eq_iff', pi.add_apply],
    split,
    { rintros rfl,
      simp only [eq_self_iff_true, dif_pos], refl, },
    { intros h,
      simp only [h, pi.zero_apply, dif_neg, not_false_iff, add_zero], }, },
  map_smul' := λ r x,
    by { ext,
    simp only [dite_apply, dite_eq_iff', pi.smul_apply],
    split,
    { rintros rfl,
      simp only [eq_self_iff_true, dif_pos], refl, },
    { intros h,
      simp only [h, pi.zero_apply, dif_neg, not_false_iff, smul_zero], }, } }

lemma include_block_mul_same {o : Type*} [fintype o] [decidable_eq o] {m' : o → Type*}
  {α : Type*}
  [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α] {i : o}
  (x y : matrix (m' i) (m' i) α) :
  (include_block x) * (include_block y) = include_block (x * y) :=
begin
  ext,
  simp_rw [include_block, linear_map.coe_mk, pi.mul_apply, mul_dite, dite_mul, mul_zero,
    zero_mul, dite_apply, pi.zero_apply],
  simp only [eq_mp_eq_cast, mul_eq_mul, dite_eq_ite, if_t_t],
  congr,
  ext,
  simp only [x_2, eq_self_iff_true, eq_mp_eq_cast, mul_eq_mul, dif_pos, mul_apply, cast],
  finish,
end

lemma include_block_mul_ne_same {o : Type*} [fintype o] [decidable_eq o] {m' : o → Type*}
  {α : Type*}
  [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α] {i j : o}
  (h : i ≠ j) (x : matrix (m' i) (m' i) α) (y : matrix (m' j) (m' j) α) :
  (include_block x) * (include_block y) = 0 :=
begin
  ext,
  simp_rw [include_block, linear_map.coe_mk, pi.mul_apply, mul_dite, dite_mul, mul_zero,
    zero_mul, dite_apply, pi.zero_apply],
  simp only [eq_mp_eq_cast, mul_eq_mul, dite_eq_ite, if_t_t],
  finish,
end

lemma include_block_mul {o : Type*} [fintype o] [decidable_eq o] {m' : o → Type*}
  {α : Type*}
  [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α] {i : o}
  (x : matrix (m' i) (m' i) α) (y : Π j, matrix (m' j) (m' j) α) :
  (include_block x) * y = include_block (x * (y i)) :=
begin
  ext,
  simp only [include_block, linear_map.coe_mk, pi.mul_apply, dite_mul, zero_mul,
    dite_apply, pi.zero_apply],
  split_ifs; simp,
  finish,
end

lemma mul_include_block {o : Type*} [fintype o] [decidable_eq o] {m' : o → Type*}
  {α : Type*}
  [Π i, fintype (m' i)] [Π i, decidable_eq (m' i)] [comm_semiring α] {i : o}
  (x : Π j, matrix (m' j) (m' j) α) (y : matrix (m' i) (m' i) α) :
  x * (include_block y) = include_block ((x i) * y) :=
begin
  ext,
  simp only [include_block, linear_map.coe_mk, pi.mul_apply, dite_mul, zero_mul,
    dite_apply, pi.zero_apply],
  split_ifs; simp,
  finish,
end

open_locale big_operators
lemma sum_include_block {R k : Type*} [comm_semiring R] [fintype k]
  [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (x : Π i, matrix (s i) (s i) R) :
  ∑ i, include_block (x i) = x :=
begin
  ext,
  simp only [finset.sum_apply, include_block, linear_map.coe_mk, dite_apply, pi.zero_apply,
    finset.sum_dite_eq', finset.mem_univ, if_true],
  refl,
end

lemma block_diagonal'_include_block_trace {R k : Type*} [comm_semiring R] [fintype k]
  [decidable_eq k] {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (x : Π i, matrix (s i) (s i) R) (j : k) :
  (block_diagonal' (include_block (x j))).trace = (x j).trace :=
begin
  calc (block_diagonal' (include_block (x j))).trace
    = ∑ i, (include_block (x j) i).trace : _
  ... = (x j).trace : _,
  { simp_rw [matrix.trace, matrix.diag, block_diagonal'_apply, eq_self_iff_true, dif_pos,
    finset.sum_sigma'],
    refl, },
  { simp only [include_block, linear_map.coe_mk, matrix.trace, matrix.diag,
      finset.sum_dite_irrel, finset.sum_const_zero, dite_apply, finset.sum_dite_eq,
      finset.mem_univ, if_true, pi.zero_apply],
    refl, },
end

open_locale matrix

lemma std_basis_matrix_mul_trace {R n p : Type*} [semiring R]
  [fintype p] [decidable_eq p] [fintype n] [decidable_eq n]
  (i : n) (j : p) (x : matrix p n R) :
  (std_basis_matrix i j 1 ⬝ x).trace = x j i :=
by simp_rw [matrix.trace, matrix.diag, mul_apply, std_basis_matrix, boole_mul,
  ite_and, finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq,
  finset.mem_univ, if_true]

lemma ext_iff_trace {R n p : Type*} [fintype n] [fintype p]
  [decidable_eq n] [decidable_eq p] [comm_semiring R]
  (x y : matrix n p R) :
  x = y ↔ ∀ a, (x ⬝ a).trace = (y ⬝ a).trace :=
begin
  refine ⟨λ h a, by rw h, λ h, _⟩,
  ext,
  specialize h (std_basis_matrix j i 1),
  simp_rw [trace_mul_comm _ (std_basis_matrix _ _ _), matrix.std_basis_matrix_mul_trace j i] at h,
  exact h,
end

variables {R : Type*} [comm_semiring R]

lemma is_block_diagonal.eq {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {x : matrix (Σ i, s i) (Σ i, s i) R} (hx : x.is_block_diagonal) :
  block_diagonal' (x.block_diag') = x :=
hx

lemma is_block_diagonal.add {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {x y : matrix (Σ i, s i) (Σ i, s i) R} (hx : x.is_block_diagonal)
  (hy : y.is_block_diagonal) :
  (x + y).is_block_diagonal :=
begin
  simp only [matrix.is_block_diagonal, block_diag'_add, block_diagonal'_add, hx.eq, hy.eq],
end
lemma is_block_diagonal.zero {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  (0 : matrix (Σ i, s i) (Σ i, s i) R).is_block_diagonal :=
by simp only [matrix.is_block_diagonal, block_diag'_zero, block_diagonal'_zero]

instance add_comm_monoid_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  add_comm_monoid { x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal } :=
{ add := λ x y, ⟨↑x + ↑y, matrix.is_block_diagonal.add (subtype.mem x) (subtype.mem y)⟩,
  add_assoc := λ x y z, by { simp only [subtype.eta, add_assoc, subtype.coe_mk], },
  zero := ⟨(0 : matrix (Σ i, s i) (Σ i, s i) R), matrix.is_block_diagonal.zero⟩,
  zero_add := λ a, by { simp only [subtype.eta, subtype.coe_mk, zero_add, subtype.coe_eta], },
  add_zero := λ a, by { simp only [subtype.coe_eta, subtype.coe_mk, add_zero], },
  add_comm := λ a b, by { ext,
    unfold_coes,
    simp only [subtype.val, add_comm], } }

lemma is_block_diagonal.coe_add {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {x y : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}} :
  ((x + y : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}) : matrix (Σ i, s i) (Σ i, s i) R) = x + y :=
rfl

private lemma is_block_diagonal.coe_sum_aux {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {n : ℕ}
  {x : fin n → {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}} :
  ((∑ i, x i : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}) : matrix (Σ i, s i) (Σ i, s i) R)
  = ∑ i, x i :=
begin
  induction n with d hd,
  { simp only [fintype.univ_of_is_empty, finset.sum_empty], refl, },
  { simp only [fin.sum_univ_succ, matrix.is_block_diagonal.coe_add, hd], },
end

lemma is_block_diagonal.coe_sum {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {n : Type*} [fintype n] [decidable_eq n]
  {x : n → {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}} :
  ((∑ i, x i : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}) : matrix (Σ i, s i) (Σ i, s i) R)
  = ∑ i, x i :=
begin
  let σ : fin (fintype.card n) ≃ n := (fintype.equiv_fin n).symm,
  have : ∑ (i : n), x i = ∑ (i : fin (fintype.card n)), x (σ i),
  { apply fintype.sum_equiv σ.symm,
    intros i,
    simp only [equiv.apply_symm_apply], },
  rw this,
  have : ∑ (i : n), (x i : matrix (Σ i, s i) (Σ i, s i) R) = ∑ (i : fin (fintype.card n)), x (σ i),
  { apply fintype.sum_equiv σ.symm,
    intros i,
    simp only [equiv.apply_symm_apply], },
  rw this,
  exact is_block_diagonal.coe_sum_aux,
end

lemma is_block_diagonal.coe_zero {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  ((0 : { x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal }) : matrix (Σ i, s i) (Σ i, s i) R) = 0 :=
rfl

lemma is_block_diagonal.smul  {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {x : matrix (Σ i, s i) (Σ i, s i) R} (hx : x.is_block_diagonal) (α : R) :
  (α • x).is_block_diagonal :=
begin
  simp only [matrix.is_block_diagonal, block_diag'_smul, block_diagonal'_smul, hx.eq],
end

instance has_smul_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  has_smul R {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal} :=
{ smul := λ a x, ⟨a • (x : matrix (Σ i, s i) (Σ i, s i) R), matrix.is_block_diagonal.smul (subtype.mem x) a⟩ }

lemma is_block_diagonal.coe_smul {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (a : R) (x : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}) :
  ((a • x : {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal}) : matrix (Σ i, s i) (Σ i, s i) R) = a • ↑x :=
rfl

instance mul_action_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  mul_action R {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal} :=
{ one_smul := λ x, by { simp only [← subtype.val_inj, subtype.val, one_smul], refl, },
  mul_smul := λ a b x, by { simp only [← smul_smul, ← subtype.val_inj, subtype.val], refl, } }

instance distrib_mul_action_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  distrib_mul_action R {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal} :=
{ smul_zero := λ x, by { simp only [subtype.ext_iff_val, subtype.val, matrix.is_block_diagonal.coe_zero,
    smul_zero], },
  smul_add := λ a x y, by { simp only [subtype.ext_iff_val, subtype.val,
    matrix.is_block_diagonal.coe_add, matrix.is_block_diagonal.coe_smul, smul_add], } }

instance module_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] :
  module R {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal} :=
{ add_smul := λ x y a, by { simp only [subtype.ext_iff_val, subtype.val, add_smul, matrix.is_block_diagonal.coe_smul], },
  zero_smul := λ a, by { simp only [subtype.ext_iff, matrix.is_block_diagonal.coe_smul, zero_smul],
    refl, } }

lemma is_block_diagonal.block_diagonal' {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (x : Π i, matrix (s i) (s i) R) :
  (block_diagonal' x).is_block_diagonal :=
begin
  rw [matrix.is_block_diagonal, block_diag'_block_diagonal'],
end

lemma is_block_diagonal_iff {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (x : matrix (Σ i, s i) (Σ i, s i) R) :
  x.is_block_diagonal ↔ ∃ y : (Π i, matrix (s i) (s i) R), x = block_diagonal' y :=
⟨λ h, ⟨x.block_diag', h.symm⟩,
  by rintros ⟨y, rfl⟩; exact matrix.is_block_diagonal.block_diagonal' y⟩

def std_basis_matrix_block_diagonal {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  (i : k) (j l : s i) (α : R) :
  {x : matrix (Σ i, s i) (Σ i, s i) R // x.is_block_diagonal} :=
⟨std_basis_matrix ⟨i, j⟩ ⟨i, l⟩ α, by {
    simp only [matrix.is_block_diagonal, block_diag'_apply,
      block_diagonal'_apply, matrix.block_diagonal'_ext, dite_eq_iff', cast_heq],
    intros a b c d,
    split,
    { intros h,
      congr,
      exact h,
      simp only [cast_heq], },
    { intros h,
      symmetry,
      apply std_basis_matrix.apply_of_ne,
      simp only [],
      rintros ⟨⟨rfl, h2⟩, ⟨rfl, h4⟩⟩,
      contradiction, }, }⟩


lemma include_block_conj_transpose {R k : Type*} [comm_semiring R] [star_ring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i : k} {x : matrix (s i) (s i) R} :
  star x.include_block = xᴴ.include_block :=
begin
  ext,
  simp only [pi.star_apply, matrix.include_block, linear_map.coe_mk, star_apply, dite_apply,
    pi.zero_apply, star_dite, star_zero, conj_transpose_apply],
  split_ifs; finish,
end

lemma include_block_inj {k : Type*} [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i : k} {x y : matrix (s i) (s i) R} :
  x.include_block = y.include_block ↔ x = y :=
begin
  simp only [include_block, linear_map.coe_mk],
  refine ⟨λ h, _, λ h, by rw h⟩,
  simp_rw [function.funext_iff, dite_apply, pi.zero_apply, dite_eq_iff'] at h,
  ext1 j k,
  specialize h i j k,
  cases h with h1 h2,
  specialize h1 rfl,
  simp only [eq_self_iff_true, dif_pos] at h1,
  finish,
end

lemma block_diagonal'_include_block_is_hermitian_iff {R k : Type*} [comm_semiring R]
  [star_ring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i : k}
  (x : matrix (s i) (s i) R) :
  (block_diagonal' x.include_block).is_hermitian ↔ x.is_hermitian :=
begin
  calc (block_diagonal' x.include_block).is_hermitian
    ↔ ((block_diagonal' x.include_block)ᴴ = block_diagonal' x.include_block) :
  by simp only [is_hermitian]
  ... ↔ (block_diagonal' (star x.include_block) = block_diagonal' x.include_block) :
  by simp only [block_diagonal'_conj_transpose]; refl
  ... ↔ (star x.include_block = x.include_block) : block_diagonal'_inj
  ... ↔ (xᴴ.include_block = x.include_block) :
  by { simp only [include_block_conj_transpose], }
  ... ↔ (xᴴ = x) : include_block_inj
  ... ↔ x.is_hermitian : by simp only [is_hermitian],
end

lemma matrix_eq_sum_include_block {R k : Type*} [comm_semiring R]
  [star_ring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] (x : Π i, matrix (s i) (s i) R) :
  x = ∑ i, include_block (x i) :=
(sum_include_block _).symm

lemma include_block_apply {R k : Type*} [comm_semiring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)] {i : k} (x : matrix (s i) (s i) R) (j : k) :
  include_block x j = dite (i = j) (λ h, by { rw h at x, exact x }) (λ h, 0) :=
rfl
lemma include_block_apply_same {R k : Type*} [comm_semiring R]
  [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i : k} (x : matrix (s i) (s i) R) :
  include_block x i = x :=
by rw [include_block_apply]; finish
lemma include_block_apply_ne_same {R k : Type*} [comm_semiring R]
  [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i j : k} (x : matrix (s i) (s i) R) (h : i ≠ j) :
  include_block x j = 0 :=
by simp only [include_block_apply, h, dif_neg, not_false_iff]

lemma include_block_apply_std_basis_matrix {R k : Type*} [comm_semiring R]
  [star_ring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i : k} (a b : s i) :
  include_block (std_basis_matrix a b (1 : R))
    = (std_basis_matrix (⟨i,a⟩ : Σ j, s j) (⟨i,b⟩ : Σ j, s j) (1 : R)).block_diag' :=
begin
  ext1 c,
  ext1 d e,
  simp_rw [include_block_apply, dite_apply, pi.zero_apply, block_diag'_apply,
    dite_eq_iff'],
  split,
  { rintros rfl,
    simp only [eq_mp_eq_cast, cast_eq, std_basis_matrix],
    congr;
    { simp only [eq_self_iff_true, heq_iff_eq, true_and], }, },
  { intros h,
    symmetry,
    apply std_basis_matrix.apply_of_ne,
    simp only [h, false_and, not_false_iff], },
end

lemma include_block_mul_include_block  {R k : Type*} [comm_semiring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {i j : k} (x : matrix (s i) (s i) R) (y : matrix (s j) (s j) R) :
  (include_block x) * (include_block y) =
    dite (j = i) (λ h, include_block (x * (by { rw ← h, exact y, }))) (λ h, 0) :=
begin
  ext1,
  simp [include_block, dite_mul, mul_dite, mul_zero, zero_mul, dite_apply, pi.zero_apply],
  split_ifs; finish,
end

end matrix

variables {R k : Type*} [comm_semiring R] [fintype k] [decidable_eq k]
  {s : k → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `ℍ₂` := (Π i, matrix (s i) (s i) R)
local notation `ℍ_ `i := matrix (s i) (s i) R

open matrix

lemma tensor_product.assoc_include_block
  {i j : k} :
  ↑(tensor_product.assoc R ℍ₂ ℍ₂ ℍ₂).symm ∘ₗ
    ((include_block : (ℍ_ i) →ₗ[R] ℍ₂)
      ⊗ₘ ((include_block : (ℍ_ j) →ₗ[R] ℍ₂) ⊗ₘ (include_block : (ℍ_ j) →ₗ[R] ℍ₂)))
  =
   (((include_block : (ℍ_ i) →ₗ[R] ℍ₂)
      ⊗ₘ ((include_block : (ℍ_ j) →ₗ[R] ℍ₂))) ⊗ₘ (include_block : (ℍ_ j) →ₗ[R] ℍ₂)) ∘ₗ
    ↑(tensor_product.assoc R (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm :=
begin
  apply tensor_product.ext_threefold',
  intros x y z,
  simp only [linear_map.comp_apply, linear_equiv.coe_coe, tensor_product.assoc_symm_tmul,
    tensor_product.map_tmul],
end