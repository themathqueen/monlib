/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_spec
import linear_algebra.my_matrix.basic
import linear_algebra.my_matrix.is_almost_hermitian
import linear_algebra.my_matrix.pos_eq_linear_map_is_positive
import linear_algebra.matrix.pos_def
import linear_algebra.my_tensor_product
import rep_theory.aut_mat
import preq.star_alg_equiv

/-!

# Inner automorphisms

This file defines the inner automorphism of a unitary matrix `U` as `U x U⁻¹` and proves that any star-algebraic automorphism on `Mₙ(ℂ)` is an inner automorphism.

-/

section

variables {n 𝕜 : Type*} [fintype n] [field 𝕜] [star_ring 𝕜]

@[simp] lemma star_alg_equiv.trace_preserving [decidable_eq n]
  (f : matrix n n 𝕜 ≃⋆ₐ[𝕜] matrix n n 𝕜) (x : matrix n n 𝕜) :
  (f x).trace = x.trace :=
aut_mat_inner_trace_preserving f.to_alg_equiv x

end

def unitary.inner_aut_star_alg (K : Type*) {R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (a : unitary R) :
  R ≃⋆ₐ[K] R :=
begin
  letI : invertible (a : R) :=
  ⟨star (a : R), unitary.coe_star_mul_self a, unitary.coe_mul_star_self a⟩,
  apply star_alg_equiv.of_alg_equiv (algebra.aut_inner (a : R)),
  intros x,
  simp only [algebra.aut_inner_apply, star_mul, star_star, mul_assoc],
end

lemma unitary.inner_aut_star_alg_apply {K R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (U : unitary R) (x : R) :
  unitary.inner_aut_star_alg K U x = U * x * (star U : unitary R) :=
rfl
lemma unitary.inner_aut_star_alg_apply' {K R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (U : unitary R) (x : R) :
  unitary.inner_aut_star_alg K U x = U * x * (U⁻¹ : unitary R) :=
rfl
lemma unitary.inner_aut_star_alg_symm_apply {K R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (U : unitary R) (x : R) :
  (unitary.inner_aut_star_alg K U).symm x = (star U : unitary R) * x * U :=
rfl
lemma unitary.inner_aut_star_alg_symm_apply' {K R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (U : unitary R) (x : R) :
  (unitary.inner_aut_star_alg K U).symm x = (U⁻¹ : unitary R) * x * U :=
rfl
lemma unitary.inner_aut_star_alg_symm {K R : Type*} [comm_semiring K]
  [semiring R] [star_semigroup R] [algebra K R] (U : unitary R) :
  (unitary.inner_aut_star_alg K U).symm = unitary.inner_aut_star_alg K U⁻¹ :=
begin
  ext1,
  simp only [unitary.inner_aut_star_alg_symm_apply', unitary.inner_aut_star_alg_apply', inv_inv],
end

lemma unitary.pi_coe {k : Type*} {s : k → Type*}
  [Π i, semiring (s i)] [Π i, star_semigroup (s i)]
  (U : Π i, unitary (s i)) :
  (λ i, ↑(U i) : Π i, s i) = ↑U :=
rfl

lemma unitary.pi_mem {k : Type*} {s : k → Type*}
  [Π i, semiring (s i)] [Π i, star_semigroup (s i)]
  (U : Π i, unitary (s i)) :
  ↑U ∈ @unitary (Π i, s i) _ (@pi.star_semigroup k s _ _inst_2) :=
begin
  rw [← unitary.pi_coe U, unitary.mem_iff],
  simp only [function.funext_iff, pi.mul_apply, pi.star_apply, pi.one_apply,
    unitary.coe_star_mul_self, unitary.coe_mul_star_self, eq_self_iff_true,
    and_self, implies_true_iff],
end

def unitary.pi {k : Type*} {s : k → Type*}
  [Π i, semiring (s i)] [Π i, star_semigroup (s i)] (U : Π i, unitary (s i)) :
  @unitary (Π i, s i) _ (@pi.star_semigroup k s _ _inst_2) :=
⟨↑U, unitary.pi_mem U⟩

lemma unitary.pi_apply {k : Type*} {s : k → Type*}
  [Π i, semiring (s i)] [Π i, star_semigroup (s i)] (U : Π i, unitary (s i))
  {i : k} :
  (unitary.pi U : Π i, (s i)) i = U i :=
rfl

namespace matrix

variables {n 𝕜 : Type*} [fintype n] [field 𝕜] [star_ring 𝕜]

@[simp] lemma unitary_group.mul_star_self [decidable_eq n]
  (a : matrix.unitary_group n 𝕜) :
  (matrix.mul a (star a) : matrix n n 𝕜) = (1 : matrix n n 𝕜) :=
by { rw [← matrix.mul_eq_mul, unitary.mul_star_self_of_mem _],
     exact set_like.coe_mem a, }

@[simp] lemma unitary_group.star_coe_eq_coe_star [decidable_eq n] (U : unitary_group n 𝕜) :
  (star (U : unitary_group n 𝕜) : matrix n n 𝕜) = (star U : unitary_group n 𝕜) :=
rfl

/-- given a unitary $U$, we have the inner algebraic automorphism, given by
  $x \mapsto UxU^*$ with its inverse given by $x \mapsto U^* x U$ -/
def inner_aut_star_alg [decidable_eq n] (a : unitary_group n 𝕜) :
  matrix n n 𝕜 ≃⋆ₐ[𝕜] matrix n n 𝕜 :=
unitary.inner_aut_star_alg 𝕜 a

open_locale matrix
lemma inner_aut_star_alg_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut_star_alg U x = U ⬝ x ⬝ (star U : unitary_group n 𝕜) :=
rfl
lemma inner_aut_star_alg_apply' [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut_star_alg U x = U ⬝ x ⬝ (U⁻¹ : unitary_group n 𝕜) :=
rfl
lemma inner_aut_star_alg_symm_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut_star_alg U).symm x = (star U : unitary_group n 𝕜) ⬝ x ⬝ U :=
rfl
lemma inner_aut_star_alg_symm_apply' [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut_star_alg U).symm x = (U⁻¹ : unitary_group n 𝕜) ⬝ x ⬝ U :=
rfl
@[simp] lemma inner_aut_star_alg_symm [decidable_eq n] (U : unitary_group n 𝕜) :
  (inner_aut_star_alg U).symm = inner_aut_star_alg U⁻¹ :=
unitary.inner_aut_star_alg_symm U

/-- inner automorphism (`matrix.inner_aut_star_alg`), but as a linear map -/
def inner_aut [decidable_eq n] (U : unitary_group n 𝕜) :
  matrix n n 𝕜 →ₗ[𝕜] matrix n n 𝕜 :=
(inner_aut_star_alg U).to_alg_equiv.to_linear_map

@[simp] lemma inner_aut_coe [decidable_eq n] (U : unitary_group n 𝕜) :
  ⇑(inner_aut U) = inner_aut_star_alg U :=
rfl
@[simp] lemma inner_aut_inv_coe [decidable_eq n] (U : unitary_group n 𝕜) :
  ⇑(inner_aut U⁻¹) = (inner_aut_star_alg U).symm :=
by simp_rw [inner_aut_star_alg_symm]; refl

lemma inner_aut_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U x = U ⬝ x ⬝ (U⁻¹ : unitary_group n 𝕜) :=
rfl

lemma inner_aut_apply' [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U x = U ⬝ x ⬝ (star U : unitary_group n 𝕜) :=
rfl

lemma inner_aut_inv_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U⁻¹ x = (U⁻¹ : unitary_group n 𝕜) ⬝ x ⬝ U :=
by simp only [inner_aut_apply, inv_inv _]

lemma inner_aut_star_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut (star U) x = (star U : unitary_group n 𝕜) ⬝ x ⬝ U :=
by simp_rw [inner_aut_apply', star_star]

lemma inner_aut_conj_transpose [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut U x)ᴴ = inner_aut U xᴴ :=
(star_alg_equiv.map_star' _ _).symm

lemma inner_aut_comp_inner_aut [decidable_eq n] (U₁ U₂ : unitary_group n 𝕜) :
  (inner_aut U₁) ∘ₗ (inner_aut U₂) = inner_aut (U₁ * U₂) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, inner_aut_apply,
    unitary_group.inv_apply, unitary_group.mul_apply, matrix.star_mul,
    matrix.mul_assoc, eq_self_iff_true, forall_true_iff],
end

lemma inner_aut_apply_inner_aut [decidable_eq n] (U₁ U₂ : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U₁ (inner_aut U₂ x) = inner_aut (U₁ * U₂) x :=
by rw [← inner_aut_comp_inner_aut _ _, linear_map.comp_apply]

lemma inner_aut_eq_iff [decidable_eq n] (U : unitary_group n 𝕜) (x y : matrix n n 𝕜) :
  inner_aut U x = y ↔ x = inner_aut U⁻¹ y :=
begin
  rw [inner_aut_coe, inner_aut_inv_coe, ← star_alg_equiv.symm_apply_eq,
    star_alg_equiv.symm_symm],
end

lemma unitary_group.to_linear_equiv_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : n → 𝕜) :
  (unitary_group.to_linear_equiv U) x = (↑(U : unitary_group n 𝕜) : matrix n n 𝕜).mul_vec x :=
rfl

lemma unitary_group.to_linear_equiv_eq [decidable_eq n] (U : unitary_group n 𝕜) (x : n → 𝕜) :
  (unitary_group.to_linear_equiv U) x = (unitary_group.to_lin' U) x :=
rfl

lemma unitary_group.to_lin'_apply [decidable_eq n] (U : unitary_group n 𝕜) (x : n → 𝕜) :
  (unitary_group.to_lin' U) x = (↑(U : unitary_group n 𝕜) : matrix n n 𝕜).mul_vec x :=
rfl

lemma unitary_group.to_lin'_eq [decidable_eq n] (U : unitary_group n 𝕜) (x : n → 𝕜) :
  (unitary_group.to_lin' U) x = (to_lin' U) x :=
rfl

/-- the spectrum of $U x U^*$ for any unitary $U$ is equal to the spectrum of $x$ -/
lemma inner_aut.spectrum_eq [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  spectrum 𝕜 (inner_aut U x).to_lin' = spectrum 𝕜 x.to_lin' :=
begin
  rw [inner_aut_apply, to_lin'_mul, spectrum.comm, ← to_lin'_mul, ← matrix.mul_assoc,
    unitary_group.inv_apply, unitary_group.star_mul_self, matrix.one_mul],
end

lemma inner_aut_one [decidable_eq n] :
  inner_aut (1 : unitary_group n 𝕜) = 1 :=
begin
  simp_rw [linear_map.ext_iff, inner_aut_apply, unitary_group.inv_apply,
    unitary_group.one_apply, star_one, matrix.mul_one, matrix.one_mul,
    linear_map.one_apply, eq_self_iff_true, forall_true_iff],
end

lemma inner_aut_comp_inner_aut_inv [decidable_eq n] (U : unitary_group n 𝕜) :
  inner_aut U ∘ₗ inner_aut U⁻¹ = 1 :=
begin
  rw linear_map.ext_iff,
  intros x,
  rw [linear_map.comp_apply, inner_aut_coe, inner_aut_inv_coe, star_alg_equiv.apply_symm_apply],
  refl,
end

lemma inner_aut_apply_inner_aut_inv [decidable_eq n]
  (U₁ U₂ : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U₁ (inner_aut U₂⁻¹ x) = inner_aut (U₁ * U₂⁻¹) x :=
by rw [inner_aut_apply_inner_aut]


lemma inner_aut_apply_inner_aut_inv_self [decidable_eq n]
  (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U (inner_aut U⁻¹ x) = x :=
begin
  rw [inner_aut_apply_inner_aut_inv, mul_inv_self, inner_aut_one, linear_map.one_apply],
end

lemma inner_aut_inv_apply_inner_aut_self [decidable_eq n]
  (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut U⁻¹ (inner_aut U x) = x :=
begin
  rw [inner_aut_inv_coe, inner_aut_coe],
  exact star_alg_equiv.symm_apply_apply _ _,
end

lemma inner_aut_apply_zero [decidable_eq n] (U : unitary_group n 𝕜) :
  inner_aut U 0 = 0 :=
map_zero _

/-- the spectrum of a linear map $x$ equals the spectrum of
  $f_U^{-1} x f_U$ for some unitary $U$ and $f_U$ is
  the inner automorphism (`matrix.inner_aut`) -/
lemma inner_aut_conj_spectrum_eq [decidable_eq n]
  (U : unitary_group n 𝕜) (x : matrix n n 𝕜 →ₗ[𝕜] matrix n n 𝕜) :
  spectrum 𝕜 ((inner_aut U⁻¹) ∘ₗ x ∘ₗ (inner_aut U)) = spectrum 𝕜 x :=
begin
  rw [spectrum.comm, linear_map.comp_assoc, inner_aut_comp_inner_aut_inv, linear_map.comp_one],
end

/-- the inner automorphism is unital -/
lemma inner_aut_apply_one [decidable_eq n] (U : unitary_group n 𝕜) :
  inner_aut U 1 = 1 :=
_root_.map_one (inner_aut_star_alg U)

lemma inner_aut_star_alg_apply_eq_inner_aut_apply
  [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  inner_aut_star_alg U x = inner_aut U x :=
rfl

lemma inner_aut.map_mul [decidable_eq n] (U : unitary_group n 𝕜) (x y : matrix n n 𝕜) :
  inner_aut U (x ⬝ y) = inner_aut U x ⬝ inner_aut U y :=
_root_.map_mul (inner_aut_star_alg U) _ _

lemma inner_aut.map_star [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  star (inner_aut U x) = inner_aut U (star x) :=
inner_aut_conj_transpose _ _

lemma inner_aut_inv_eq_star [decidable_eq n] {x : unitary_group n 𝕜} :
  inner_aut x⁻¹ = inner_aut (star x) :=
rfl

lemma unitary_group.coe_inv [decidable_eq n] (U : unitary_group n 𝕜) :
  ⇑(U⁻¹ : unitary_group n 𝕜) = ((U : matrix n n 𝕜)⁻¹ : matrix n n 𝕜) :=
begin
  symmetry,
  apply inv_eq_left_inv,
  simp_rw [unitary_group.inv_apply, unitary_group.star_mul_self],
end

lemma inner_aut.map_inv [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut U x)⁻¹ = inner_aut U x⁻¹ :=
begin
  simp_rw [inner_aut_apply, matrix.mul_inv_rev, ← unitary_group.coe_inv,
    inv_inv, matrix.mul_assoc],
end
/-- the trace of $f_U(x)$ is equal to the trace of $x$ -/
lemma inner_aut_apply_trace_eq [decidable_eq n] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut U x).trace = x.trace :=
star_alg_equiv.trace_preserving _ _

variables [decidable_eq n]

lemma exists_inner_aut_iff_exists_inner_aut_inv {P : matrix n n 𝕜 → Prop} (x : matrix n n 𝕜) :
  (∃ (U : unitary_group n 𝕜), P (inner_aut U x)) ↔ (∃ (U : unitary_group n 𝕜), P (inner_aut U⁻¹ x)) :=
begin
  split; rintros ⟨U, hU⟩,
  { use U⁻¹,
    simp_rw [inv_inv],
    exact hU, },
  { use U⁻¹,
    exact hU, },
end

lemma inner_aut.is_injective (U : unitary_group n 𝕜) :
  function.injective (inner_aut U) :=
begin
  intros u v huv,
  rw [← inner_aut_inv_apply_inner_aut_self U u, huv, inner_aut_inv_apply_inner_aut_self],
end

/-- $x$ is Hermitian if and only if $f_U(x)$ is Hermitian -/
lemma is_hermitian.inner_aut_iff (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  x.is_hermitian ↔ (inner_aut U x).is_hermitian :=
begin
  simp_rw [is_hermitian, inner_aut_conj_transpose,
    function.injective.eq_iff (inner_aut.is_injective U)],
end

lemma pos_semidef.inner_aut {𝕜 : Type*} [is_R_or_C 𝕜] (U : unitary_group n 𝕜) {a : matrix n n 𝕜} :
  (inner_aut U a).pos_semidef ↔ a.pos_semidef :=
begin
  split,
  { intro h,
    obtain ⟨y, hy⟩ := (pos_semidef_iff _).mp h,
    rw [inner_aut_eq_iff, inner_aut.map_mul, ← inner_aut_conj_transpose] at hy,
    rw hy,
    exact pos_semidef.star_mul_self _, },
  { intro h,
    obtain ⟨y, hy⟩ := (pos_semidef_iff _).mp h,
    rw [hy, inner_aut.map_mul, ← inner_aut_conj_transpose],
    exact pos_semidef.star_mul_self _, },
end

/-- $f_U(x)$ is positive definite if and only if $x$ is positive definite -/
lemma pos_def.inner_aut {𝕜 : Type*} [is_R_or_C 𝕜] (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  ((inner_aut U x).pos_def ↔ x.pos_def) :=
begin
  let D := inner_aut U x,
  have hD : inner_aut U x = D := rfl,
  have hD' := hD,
  rw [inner_aut_eq_iff] at hD',
  rw [hD', inner_aut_inv_apply_inner_aut_self],
  simp_rw [pos_def, ← is_hermitian.inner_aut_iff U, inner_aut_apply, ← mul_vec_mul_vec,
    dot_product_mul_vec _ U],
  have ugh : ∀ (u : n → 𝕜) (v : matrix n n 𝕜), vec_mul (star u) v = star (mul_vec (star v) u),
  { intros,
    ext1,
    simp_rw [pi.star_apply, vec_mul, mul_vec, dot_product, star_sum, star_mul',
      star_apply, star_star, pi.star_apply, mul_comm], },
  simp_rw [ugh, ← unitary_group.inv_apply],
  have ugh' : ∀ (hi : unitary_group n 𝕜) (u : n → 𝕜), mul_vec (hi : _) u ≠ 0 ↔ u ≠ 0,
  { intros,
    rw [ne.def, ← to_lin'_apply, ← unitary_group.to_lin'_eq,
      ← unitary_group.to_linear_equiv_eq, (injective_iff_map_eq_zero' _).mp
        (linear_equiv.injective (unitary_group.to_linear_equiv hi))], },
  refine ⟨λ h, ⟨h.1, λ u hu, _⟩, λ h, ⟨h.1, λ u hu, h.2 _ ((ugh' _ _).mpr hu)⟩⟩,
  { rcases h with ⟨h1, h2⟩,
    specialize h2 (mul_vec U u) ((ugh' _ _).mpr hu),
    simp_rw [mul_vec_mul_vec, unitary_group.inv_apply, unitary_group.star_mul_self,
      one_mul_vec, matrix.mul_one] at h2,
    exact h2, },
end

/-- Schur decomposition, but only for almost Hermitian matrices:
  given an almost Hermitian matrix $A$, there exists a diagonal matrix $D$ and
  a unitary matrix $U$ such that $UDU^*=A$ -/
lemma is_almost_hermitian.schur_decomp {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  {A : matrix n n 𝕜} (hA : A.is_almost_hermitian) :
  ∃ (D : n → 𝕜) (U : unitary_group n 𝕜),
    inner_aut U (diagonal D) = A :=
begin
  rcases hA with ⟨α, B, ⟨rfl, hB⟩⟩,
  have : hB.eigenvector_matrix ∈ unitary_group n 𝕜,
  { rw [mem_unitary_group_iff, mul_eq_mul, star_eq_conj_transpose,
      is_hermitian.conj_transpose_eigenvector_matrix, is_hermitian.eigenvector_matrix_mul_inv], },
  let U : unitary_group n 𝕜 := ⟨_, this⟩,
  have hU : ⇑U = hB.eigenvector_matrix := rfl,
  use α • (coe ∘ hB.eigenvalues),
  use U,
  simp_rw [diagonal_smul, smul_hom_class.map_smul, inner_aut_apply, unitary_group.inv_apply,
    star_eq_conj_transpose, hU, is_hermitian.conj_transpose_eigenvector_matrix, matrix.mul_assoc,
    ← is_hermitian.spectral_theorem, ← matrix.mul_assoc, is_hermitian.eigenvector_matrix_mul_inv,
    matrix.one_mul],
end

/-- any $^*$-isomorphism on $M_n$ is an inner automorphism -/
lemma star_alg_equiv.of_matrix_is_inner {𝕜 : Type*} [is_R_or_C 𝕜]
  (f : matrix n n 𝕜 ≃⋆ₐ[𝕜] matrix n n 𝕜) :
  ∃ U : unitary_group n 𝕜, inner_aut_star_alg U = f :=
begin
  by_cases is_empty n,
  { haveI := h,
    use 1,
    ext,
    have : a = 0 := by simp only [eq_iff_true_of_subsingleton],
    simp_rw [this, map_zero], },
  rw not_is_empty_iff at h,
  haveI := h,
  let f' := f.to_alg_equiv,
  obtain ⟨y', hy⟩ := aut_mat_inner f',
  let y := y'.to_linear_map.to_matrix',
  let yinv := y'.symm.to_linear_map.to_matrix',
  have Hy : y ⬝ yinv = 1 ∧ yinv ⬝ y = 1,
  { simp_rw [y, yinv, linear_equiv.to_linear_map_eq_coe, ← linear_map.to_matrix'_comp,
      linear_equiv.comp_coe, linear_equiv.symm_trans_self, linear_equiv.self_trans_symm,
      linear_equiv.refl_to_linear_map, linear_map.to_matrix'_id, and_self], },
  have H : y⁻¹ = yinv := inv_eq_left_inv Hy.2,
  have hf' : ∀ x : matrix n n 𝕜, f' x = y ⬝ x ⬝ y⁻¹,
  { intros x,
    simp_rw [hy, algebra.aut_inner_apply, H, mul_eq_mul],
    refl, },
  have hf : ∀ x : matrix n n 𝕜, f x = y ⬝ x ⬝ y⁻¹,
  { intros x,
    rw ← hf',
    refl, },
  have this : ∀ x : matrix n n 𝕜, (f x)ᴴ = f xᴴ := λ _, (star_alg_equiv.map_star' _ _).symm,
  simp_rw [hf, conj_transpose_mul, conj_transpose_nonsing_inv] at this,
  have this3 : ∀ x : matrix n n 𝕜, (yᴴ ⬝ y) ⬝ xᴴ ⬝ y⁻¹ = xᴴ ⬝ yᴴ,
  { intros x,
    simp_rw [matrix.mul_assoc, ← matrix.mul_assoc y, ← this, ← matrix.mul_assoc,
      ← conj_transpose_nonsing_inv, ← conj_transpose_mul, H, Hy.2, matrix.mul_one], },
  have this2 : ∀ x : matrix n n 𝕜, commute xᴴ (yᴴ ⬝ y),
  { intros x,
    simp_rw [commute, semiconj_by, mul_eq_mul, ← matrix.mul_assoc, ← this3, matrix.mul_assoc,
      H, Hy.2, matrix.mul_one], },
  have this4 : ∀ x : matrix n n 𝕜, commute x (yᴴ ⬝ y),
  { intros,
    specialize this2 xᴴ,
    simp_rw [conj_transpose_conj_transpose] at this2,
    exact this2, },
  obtain ⟨α, hα⟩ := commutes_with_all_iff.mp this4,
  have this6 : to_euclidean_lin (1 : matrix n n 𝕜) = 1,
  { ext1, ext1, simp only [linear_map.one_apply, to_euclidean_lin_eq_to_lin,
      to_lin_apply, one_mul_vec, smul_eq_mul],
    simp only [pi_Lp.basis_fun_repr, pi_Lp.basis_fun_apply, pi_Lp.equiv_symm_single,
      finset.sum_apply, pi.smul_apply, euclidean_space.single_apply, smul_ite, smul_zero,
      finset.sum_ite_eq, finset.mem_univ, if_true],
    rw [smul_eq_mul, mul_one], },
  have this7 : function.bijective (yᴴ ⬝ y).to_lin',
  { rw [function.bijective_iff_has_inverse],
    use (y⁻¹ ⬝ y⁻¹ᴴ).to_lin',
    simp_rw [function.left_inverse, function.right_inverse, function.left_inverse,
      ← to_lin'_mul_apply, matrix.mul_assoc, ← matrix.mul_assoc y⁻¹ᴴ, ← conj_transpose_mul, H, ← matrix.mul_assoc y],
    simp only [Hy.2, Hy.1, conj_transpose_one, matrix.mul_one, matrix.one_mul,
      to_lin'_one, linear_map.id_apply, eq_self_iff_true, forall_true_iff],
    simp_rw [← conj_transpose_mul, Hy.2, conj_transpose_one, to_lin'_one,
      linear_map.id_apply, eq_self_iff_true, forall_true_iff, true_and], },
  have this8 : (yᴴ ⬝ y).pos_semidef := pos_semidef.star_mul_self _,
  have this9 := (pos_semidef.invertible_iff_pos_def this8).mp this7,
  have this12 : (1 : n → 𝕜) ≠ 0,
  { simp_rw [ne.def, function.funext_iff, pi.one_apply, pi.zero_apply,
      one_ne_zero],
    simp only [not_forall, not_false_iff, exists_const], },
  have this10 : α = is_R_or_C.re α,
  { have this10 := is_hermitian.coe_re_diag this8.1,
    simp_rw [hα, diag_smul, diag_one, pi.smul_apply, pi.one_apply, algebra.id.smul_eq_mul,
      mul_one] at this10,
    have this11 : ((is_R_or_C.re α) : 𝕜) • (1 : n → 𝕜) = α • 1,
    { rw ← this10,
      ext1,
      simp only [pi.smul_apply, pi.one_apply, smul_eq_mul, mul_one], },
    rw (smul_left_injective _ _).eq_iff at this11,
    rw this11,
    { exact module.free.no_zero_smul_divisors 𝕜 (n → 𝕜), },
    { exact this12, }, },
  have this13 : star (1 : n → 𝕜) ⬝ᵥ (1 : n → 𝕜) = fintype.card n,
  { simp only [dot_product, pi.star_apply, pi.one_apply, star_one, one_mul,
      finset.sum_const],
    simp only [nat.smul_one_eq_coe, nat.cast_inj],
    refl, },
  simp_rw [hα, pos_def, smul_mul_vec_assoc, dot_product_smul, one_mul_vec, smul_eq_mul] at this9,
  cases this9 with this9l this9,
  specialize this9 1 this12,
  rw [this10, this13, is_R_or_C.of_real_mul_re, mul_pos_iff] at this9,
  simp_rw [is_R_or_C.nat_cast_re, nat.cast_pos, fintype.card_pos] at this9,
  have this14 : ¬ ((fintype.card n : ℝ) < 0),
  { simp only [not_lt, nat.cast_nonneg], },
  simp_rw [this14, and_false, and_true, or_false] at this9,
  have fin : (((is_R_or_C.re α : ℝ) ^ -(1 / 2 : ℝ) : ℝ) : 𝕜) • y ∈ unitary_group n 𝕜,
  { rw [mem_unitary_group_iff', star_eq_conj_transpose, mul_eq_mul],
    simp_rw [conj_transpose_smul, is_R_or_C.star_def, matrix.smul_mul,
      matrix.mul_smul, is_R_or_C.conj_of_real, smul_smul, ← is_R_or_C.of_real_mul],
    rw [← real.rpow_add this9, hα, this10, smul_smul, ← is_R_or_C.of_real_mul,
      is_R_or_C.of_real_re, ← real.rpow_add_one (norm_num.ne_zero_of_pos _ this9)],
    norm_num, },
  let U : unitary_group n 𝕜 := ⟨_, fin⟩,
  have hU : (U : matrix n n 𝕜) = (((is_R_or_C.re α : ℝ) ^ -(1 / 2 : ℝ) : ℝ) : 𝕜) • y := rfl,
  have hU2 : ((((is_R_or_C.re α : ℝ) ^ -(1 / 2 : ℝ) : ℝ) : 𝕜) • y)⁻¹ = ((U⁻¹ : _) : matrix n n 𝕜),
  { apply inv_eq_left_inv,
    rw [← hU, unitary_group.inv_apply, unitary_group.star_mul_self], },
  have hU3 : ((((is_R_or_C.re α : ℝ) ^ -(1 / 2 : ℝ) : ℝ) : 𝕜) • y)⁻¹ = (((is_R_or_C.re α : ℝ) ^ -(1 / 2 : ℝ) : ℝ) : 𝕜)⁻¹ • y⁻¹,
  { apply inv_eq_left_inv,
    simp_rw [matrix.smul_mul, matrix.mul_smul, smul_smul],
    rw [inv_mul_cancel, one_smul, H, Hy.2],
    { simp_rw [ne.def, is_R_or_C.of_real_eq_zero,
        real.rpow_eq_zero_iff_of_nonneg (le_of_lt this9),
        norm_num.ne_zero_of_pos _ this9, false_and],
      exact not_false, }, },
  use U,
  ext1 x,
  simp_rw [inner_aut_star_alg_apply_eq_inner_aut_apply, inner_aut_apply, hf, hU,
    ← hU2, hU3, matrix.smul_mul, matrix.mul_smul, smul_smul, ← is_R_or_C.of_real_inv,
    ← is_R_or_C.of_real_mul, ← real.rpow_neg_one, ← real.rpow_mul (le_of_lt this9),
    ← real.rpow_add this9],
  norm_num,
end

noncomputable def star_alg_equiv.unitary {𝕜 : Type*} [is_R_or_C 𝕜]
  (f : matrix n n 𝕜 ≃⋆ₐ[𝕜] matrix n n 𝕜) :
  unitary_group n 𝕜 :=
begin
  choose U hU using f.of_matrix_is_inner,
  exact U,
end

def star_alg_equiv.eq_inner_aut {𝕜 : Type*} [is_R_or_C 𝕜] (f : matrix n n 𝕜 ≃⋆ₐ[𝕜] matrix n n 𝕜) :
  inner_aut_star_alg f.unitary = f :=
star_alg_equiv.unitary._proof_2 f

lemma is_hermitian.spectral_theorem' {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  {x : matrix n n 𝕜} (hx : x.is_hermitian) :
  x = inner_aut ⟨_, hx.eigenvector_matrix_mem_unitary_group⟩ (diagonal (coe ∘ hx.eigenvalues)) :=
begin
  rw [inner_aut_apply, unitary_group.inv_apply, matrix.unitary_group.coe_mk,
    star_eq_conj_transpose, is_hermitian.conj_transpose_eigenvector_matrix],
  simp_rw [matrix.mul_assoc, ← is_hermitian.spectral_theorem hx, ← matrix.mul_assoc,
    is_hermitian.eigenvector_matrix_mul_inv, matrix.one_mul],
end

lemma coe_diagonal_eq_diagonal_coe {𝕜 : Type*} [is_R_or_C 𝕜] (x : n → ℝ) :
  (diagonal (coe ∘ x) : matrix n n 𝕜) = coe ∘ (diagonal x) :=
begin
  simp_rw [← matrix.ext_iff, diagonal, function.comp_apply, of_apply],
  intros,
  have : ((↑(((of (λ (i j : n), ite (i = j) (x i) 0) : matrix n n ℝ) i : n → ℝ)) : n → 𝕜) j : 𝕜)
    = ↑(of (λ i j : n, ite (i = j) (x i) 0) i j) := rfl,
  simp_rw [this, of_apply, ite_cast, is_R_or_C.of_real_zero],
end

lemma diagonal.spectrum [decidable_eq 𝕜] (A : n → 𝕜) :
  spectrum 𝕜 (diagonal A : matrix n n 𝕜).to_lin' = {x : 𝕜 | ∃ i : n, A i = x} :=
begin
  simp_rw [set.ext_iff, ← module.End.has_eigenvalue_iff_mem_spectrum,
    ← module.End.has_eigenvector_iff_has_eigenvalue, to_lin'_apply, function.funext_iff,
    mul_vec, diagonal_dot_product, pi.smul_apply, algebra.id.smul_eq_mul,
    mul_eq_mul_right_iff, ne.def, set.mem_set_of_eq, function.funext_iff,
    pi.zero_apply, not_forall],
  intros x,
  split,
  { rintros ⟨v, ⟨h, ⟨j, hj⟩⟩⟩,
    specialize h j,
    cases h,
    { exact ⟨j, h⟩, },
    { contradiction, }, },
  { rintros ⟨i, hi⟩,
    let v : n → 𝕜 := λ j, ite (j = i) 1 0,
    use v,
    simp_rw [v, ite_eq_right_iff, one_ne_zero, imp_false, not_not],
    split,
    { intros j,
      by_cases j = i,
      { left,
        rw [h, hi], },
      { right,
        exact h, }, },
    { use i, }, },
end

lemma is_hermitian.spectrum {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  {x : matrix n n 𝕜} (hx : x.is_hermitian) :
  spectrum 𝕜 x.to_lin' = {x : 𝕜 | ∃ i : n, (hx.eigenvalues i : 𝕜) = x} :=
begin
  nth_rewrite_lhs 0 matrix.is_hermitian.spectral_theorem' hx,
  simp_rw [inner_aut.spectrum_eq, diagonal.spectrum],
end

lemma is_hermitian.has_eigenvalue_iff {𝕜 : Type*} [is_R_or_C 𝕜]
  [decidable_eq 𝕜] {x : matrix n n 𝕜} (hx : x.is_hermitian) (α : 𝕜) :
  module.End.has_eigenvalue x.to_lin' α ↔ ∃ i, (hx.eigenvalues i : 𝕜) = α :=
begin
  rw [module.End.has_eigenvalue_iff_mem_spectrum, hx.spectrum, set.mem_set_of],
end

-- MOVE:
lemma inner_aut_commutes_with_map_lid_symm (U : matrix.unitary_group n 𝕜) :
  (tensor_product.map 1 (inner_aut U)) ∘ₗ (tensor_product.lid 𝕜 (matrix n n 𝕜)).symm.to_linear_map
    = (tensor_product.lid 𝕜 (matrix n n 𝕜)).symm.to_linear_map ∘ₗ (inner_aut U) :=
by simp_rw [linear_map.ext_iff, linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
     linear_equiv.coe_coe, tensor_product.lid_symm_apply, tensor_product.map_tmul,
     linear_map.one_apply, eq_self_iff_true, forall_const]


-- MOVE:
lemma inner_aut_commutes_with_lid_comm (U : matrix.unitary_group n 𝕜) :
  (tensor_product.lid 𝕜 (matrix n n 𝕜)).to_linear_map ∘ₗ
    (tensor_product.comm 𝕜 (matrix n n 𝕜) 𝕜).to_linear_map ∘ₗ (tensor_product.map (inner_aut U) 1)
    = (inner_aut U) ∘ₗ (tensor_product.lid 𝕜 (matrix n n 𝕜)).to_linear_map ∘ₗ
      (tensor_product.comm 𝕜 (matrix n n 𝕜) 𝕜).to_linear_map :=
by simp_rw [tensor_product.ext_iff, linear_map.comp_apply, tensor_product.map_apply,
  linear_equiv.to_linear_map_eq_coe, linear_equiv.coe_coe, tensor_product.comm_tmul,
  tensor_product.lid_tmul, linear_map.one_apply, smul_hom_class.map_smul,
  eq_self_iff_true, forall_2_true_iff]

lemma unitary_group.conj_mem {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  (U : unitary_group n 𝕜) :
  (U : matrix n n 𝕜)ᴴᵀ ∈ unitary_group n 𝕜 :=
begin
  rw [mem_unitary_group_iff'],
  calc star (U : matrix n n 𝕜)ᴴᵀ * (U : matrix n n 𝕜)ᴴᵀ =
    (U : _)ᴴᵀᴴ * (U : _)ᴴᵀ : rfl
    ... = ((U : _)ᴴ * (U : _))ᴴᵀ : by simp_rw [mul_eq_mul, matrix.conj_mul]; refl
    ... = 1ᴴᵀ : by rw [← star_eq_conj_transpose, mul_eq_mul, unitary_group.star_mul_self]
    ... = 1 : matrix.conj_one,
end

def unitary_group.conj {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  (U : unitary_group n 𝕜) :
  unitary_group n 𝕜 :=
⟨(U : _)ᴴᵀ, unitary_group.conj_mem U⟩

@[norm_cast] lemma unitary_group.conj_coe {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  (U : unitary_group n 𝕜) :
  (unitary_group.conj U : matrix n n 𝕜) = Uᴴᵀ :=
rfl

lemma inner_aut.conj {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]
  (U : unitary_group n 𝕜) (x : matrix n n 𝕜) :
  (inner_aut U x)ᴴᵀ = inner_aut (unitary_group.conj U) xᴴᵀ :=
begin
  simp_rw [inner_aut_apply, matrix.conj_mul, unitary_group.inv_apply,
    unitary_group.conj_coe],
  refl,
end

open_locale kronecker
lemma kronecker_mem_unitary_group {p : Type*} [fintype p] [decidable_eq p]
  [decidable_eq 𝕜] (U₁ : unitary_group n 𝕜) (U₂ : unitary_group p 𝕜) :
  (U₁ ⊗ₖ U₂) ∈ unitary_group (n × p) 𝕜 :=
begin
  simp_rw [mem_unitary_group_iff, star_eq_conj_transpose, kronecker_conj_transpose, mul_eq_mul,
    ← mul_kronecker_mul, ← star_eq_conj_transpose, unitary_group.mul_star_self, one_kronecker_one],
end

def unitary_group.kronecker {p : Type*} [fintype p] [decidable_eq p] [decidable_eq 𝕜]
  (U₁ : unitary_group n 𝕜) (U₂ : unitary_group p 𝕜) :
  unitary_group (n × p) 𝕜 :=
⟨U₁ ⊗ₖ U₂, kronecker_mem_unitary_group _ _⟩

lemma unitary_group.kronecker_coe {p : Type*} [fintype p] [decidable_eq p]
  [decidable_eq 𝕜] (U₁ : unitary_group n 𝕜) (U₂ : unitary_group p 𝕜) :
  (unitary_group.kronecker U₁ U₂ : matrix _ _ 𝕜) = U₁ ⊗ₖ U₂ :=
rfl

lemma inner_aut_kronecker {p : Type*} [fintype p] [decidable_eq p] [decidable_eq 𝕜]
  (U₁ : unitary_group n 𝕜) (U₂ : unitary_group p 𝕜) (x : matrix n n 𝕜) (y : matrix p p 𝕜) :
  inner_aut U₁ x ⊗ₖ inner_aut U₂ y = inner_aut (unitary_group.kronecker U₁ U₂) (x ⊗ₖ y) :=
begin
  simp_rw [inner_aut_apply, unitary_group.inv_apply, unitary_group.kronecker_coe,
    star_eq_conj_transpose, kronecker_conj_transpose, ← mul_kronecker_mul],
end


lemma pos_semidef.kronecker  {𝕜 n p : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  [fintype n] [fintype p] [decidable_eq n] [decidable_eq p] {x : matrix n n 𝕜}
  {y : matrix p p 𝕜} (hx : x.pos_semidef) (hy : y.pos_semidef) :
  (x ⊗ₖ y).pos_semidef :=
begin
  rw [matrix.is_hermitian.spectral_theorem' hx.1, matrix.is_hermitian.spectral_theorem' hy.1,
    inner_aut_kronecker, diagonal_kronecker_diagonal, pos_semidef.inner_aut, pos_semidef.diagonal],
  simp_rw [function.comp_apply, ← is_R_or_C.of_real_mul, is_R_or_C.of_real_re,
    eq_self_iff_true, and_true, mul_nonneg (is_hermitian.nonneg_eigenvalues_of_pos_semidef hx _)
      (is_hermitian.nonneg_eigenvalues_of_pos_semidef hy _),
    forall_true_iff],
end

lemma pos_def.kronecker {𝕜 n p : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  [fintype n] [fintype p] [decidable_eq n] [decidable_eq p] {x : matrix n n 𝕜}
  {y : matrix p p 𝕜} (hx : x.pos_def) (hy : y.pos_def) :
  (x ⊗ₖ y).pos_def :=
begin
  rw [matrix.is_hermitian.spectral_theorem' hx.1, matrix.is_hermitian.spectral_theorem' hy.1,
    inner_aut_kronecker, pos_def.inner_aut, diagonal_kronecker_diagonal, pos_def.diagonal],
  simp_rw [function.comp_apply, ← is_R_or_C.of_real_mul, is_R_or_C.of_real_re,
    eq_self_iff_true, and_true, mul_pos (hx.pos_eigenvalues _) (hy.pos_eigenvalues _),
    forall_true_iff],
end

lemma unitary_group.injective_mul {n 𝕜 : Type*} [fintype n] [decidable_eq n]
  [is_R_or_C 𝕜] [decidable_eq 𝕜]
  (U : unitary_group n 𝕜) (x y : matrix n n 𝕜) :
  x = y ↔ x ⬝ U = y ⬝ U :=
begin
  refine ⟨λ h, by rw h, λ h, _⟩,
  nth_rewrite_rhs 0 ← matrix.mul_one y,
  rw [← unitary_group.mul_star_self U, ← matrix.mul_assoc, ← h, matrix.mul_assoc,
    unitary_group.mul_star_self, matrix.mul_one],
end

lemma inner_aut_star_alg_equiv_to_linear_map {n 𝕜 : Type*} [fintype n] [decidable_eq n]
  [is_R_or_C 𝕜] [decidable_eq 𝕜] (U : unitary_group n 𝕜) :
  (inner_aut_star_alg U).to_alg_equiv.to_linear_map = inner_aut U :=
rfl
lemma inner_aut_star_alg_equiv_symm_to_linear_map {n 𝕜 : Type*} [fintype n] [decidable_eq n]
  [is_R_or_C 𝕜] [decidable_eq 𝕜] (U : unitary_group n 𝕜) :
  (inner_aut_star_alg U).symm.to_alg_equiv.to_linear_map = inner_aut U⁻¹ :=
begin
  ext1,
  simp only [inner_aut_star_alg_symm_apply, inner_aut_apply, inv_inv,
    alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv],
  rw unitary_group.inv_apply,
  refl,
end


lemma inner_aut.comp_inj {n 𝕜 : Type*} [fintype n] [decidable_eq n]
  [is_R_or_C 𝕜] [decidable_eq 𝕜] (U : matrix.unitary_group n 𝕜) (S T : matrix n n 𝕜 →ₗ[𝕜] matrix n n 𝕜) :
  S = T ↔ inner_aut U ∘ₗ S = inner_aut U ∘ₗ T :=
begin
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, inner_aut_eq_iff,
    inner_aut_inv_apply_inner_aut_self],
end

lemma inner_aut.inj_comp {n 𝕜 : Type*} [fintype n] [decidable_eq n]
  [is_R_or_C 𝕜] [decidable_eq 𝕜] (U : unitary_group n 𝕜) (S T : matrix n n 𝕜 →ₗ[𝕜] matrix n n 𝕜) :
  S = T ↔ S ∘ₗ inner_aut U = T ∘ₗ inner_aut U :=
begin
  refine ⟨λ h, by rw h, λ h, _⟩,
  simp_rw [linear_map.ext_iff, linear_map.comp_apply] at h ⊢,
  intros x,
  nth_rewrite_lhs 0 ← inner_aut_apply_inner_aut_inv_self U x,
  rw [h, inner_aut_apply_inner_aut_inv_self],
end

end matrix

