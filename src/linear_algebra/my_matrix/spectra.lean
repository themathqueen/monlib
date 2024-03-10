import linear_algebra.my_matrix.basic
import linear_algebra.inner_aut


instance multiset_coe {α β : Type*} [has_coe α β] :
  has_coe (multiset α) (multiset β) :=
{ coe := λ s, s.map (coe : α → β) }
lemma finset.val.map_coe {α β γ : Type*}
  (f : α → β) (s : finset α) [has_coe β γ] :
  ((s.val.map f : multiset β) : multiset γ) = s.val.map ↑f :=
begin
  unfold_coes,
  simp only [multiset.map_map, function.comp_app, add_monoid_hom.to_fun_eq_coe],
end

noncomputable instance multiset_coe_R_to_is_R_or_C {𝕜 : Type*} [is_R_or_C 𝕜] :
  has_coe (multiset ℝ) (multiset 𝕜) :=
@multiset_coe ℝ 𝕜 ⟨coe⟩

namespace matrix

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n] [decidable_eq 𝕜]

open_locale matrix

noncomputable def is_almost_hermitian.scalar {n : Type*}
  {x : matrix n n 𝕜} (hx : x.is_almost_hermitian) :
  𝕜 :=
by choose α hα using hx; exact α
noncomputable def is_almost_hermitian.matrix {n : Type*}
  {x : matrix n n 𝕜} (hx : x.is_almost_hermitian) :
  matrix n n 𝕜 :=
by choose y hy using (is_almost_hermitian.scalar._proof_1 hx); exact y
lemma is_almost_hermitian.eq_smul_matrix
  {n : Type*} {x : matrix n n 𝕜} (hx : x.is_almost_hermitian) :
  x = hx.scalar • hx.matrix :=
(is_almost_hermitian.matrix._proof_1 hx).1.symm
lemma is_almost_hermitian.matrix_is_hermitian
  {n : Type*} {x : matrix n n 𝕜} (hx : x.is_almost_hermitian) :
  hx.matrix.is_hermitian :=
(is_almost_hermitian.matrix._proof_1 hx).2

noncomputable def is_almost_hermitian.eigenvalues {x : matrix n n 𝕜}
  (hx : x.is_almost_hermitian) :
  n → 𝕜 :=
begin
  intros i,
  exact hx.scalar • hx.matrix_is_hermitian.eigenvalues i,
end

noncomputable def is_almost_hermitian.spectra {A : matrix n n 𝕜} (hA : A.is_almost_hermitian) : multiset 𝕜 :=
finset.univ.val.map (λ i, hA.eigenvalues i)

noncomputable def is_hermitian.spectra {A : matrix n n 𝕜} (hA : A.is_hermitian) : multiset ℝ :=
finset.univ.val.map (λ i, hA.eigenvalues i)

lemma is_hermitian.spectra_coe {A : matrix n n 𝕜} (hA : A.is_hermitian) :
  (hA.spectra : multiset 𝕜) = finset.univ.val.map (λ i, hA.eigenvalues i) :=
begin
  unfold_coes,
  simp only [multiset.map_map, is_hermitian.spectra],
end

open_locale big_operators
lemma is_hermitian.mem_coe_spectra_diagonal {A : n → 𝕜} (hA : (diagonal A).is_hermitian)
  (x : 𝕜) :
  x ∈ (hA.spectra : multiset 𝕜) ↔ ∃ (i : n), A i = x :=
begin
  simp_rw [is_hermitian.spectra_coe, multiset.mem_map],
  simp only [finset.mem_univ_val, true_and],
  have : ((x : 𝕜) ∈ {b : 𝕜 | ∃ a, ↑(hA.eigenvalues a) = b}
    ↔ (x : 𝕜) ∈ {b : 𝕜 | ∃ a, A a = b})
    ↔
    ((∃ a, (hA.eigenvalues a : 𝕜) = x) ↔ (∃ a, A a = x)),
  { simp_rw [set.mem_set_of], },
  rw ← this,
  clear this,
  revert x,
  rw [← set.ext_iff, ← is_hermitian.spectrum, diagonal.spectrum],
end
lemma is_hermitian.spectra_set_eq_spectrum
  {A : matrix n n 𝕜} (hA : A.is_hermitian) :
  {x : 𝕜 | x ∈ (hA.spectra : multiset 𝕜)}
    = spectrum 𝕜 (to_lin' A) :=
begin
  ext,
  simp_rw [is_hermitian.spectra_coe, hA.spectrum, set.mem_set_of,
    multiset.mem_map, finset.mem_univ_val, true_and],
end

lemma is_hermitian.of_inner_aut {A : matrix n n 𝕜} (hA : A.is_hermitian)
  (U : unitary_group n 𝕜) :
  (inner_aut U A).is_hermitian :=
(is_hermitian.inner_aut_iff U A).mp hA

lemma is_almost_hermitian_iff_smul {A : matrix n n 𝕜} :
  A.is_almost_hermitian ↔ ∀ α : 𝕜, (α • A).is_almost_hermitian :=
begin
  split,
  { rintros ⟨β, y, rfl, hy⟩ α,
    rw [smul_smul],
    exact ⟨α * β, y, rfl, hy⟩, },
  { intros h,
    specialize h 1,
    rw one_smul at h,
    exact h, },
end

lemma is_almost_hermitian.smul {A : matrix n n 𝕜} (hA : A.is_almost_hermitian) (α : 𝕜) :
  (α • A).is_almost_hermitian :=
is_almost_hermitian_iff_smul.mp hA _

lemma is_almost_hermitian.of_inner_aut {A : matrix n n 𝕜} (hA : A.is_almost_hermitian)
  (U : unitary_group n 𝕜) :
  (inner_aut U A).is_almost_hermitian :=
begin
  obtain ⟨α, y, rfl, hy⟩ := hA,
  refine ⟨α, inner_aut U y, _, hy.of_inner_aut _⟩,
  simp_rw [smul_hom_class.map_smul],
end

lemma is_almost_hermitian_iff_of_inner_aut {A : matrix n n 𝕜} (U : unitary_group n 𝕜) :
  A.is_almost_hermitian ↔ (inner_aut U A).is_almost_hermitian :=
begin
  refine ⟨λ h, h.of_inner_aut _, _⟩,
  rintros ⟨α, y, h, hy⟩,
  rw [eq_comm, inner_aut_eq_iff] at h,
  rw [h, smul_hom_class.map_smul],
  clear h,
  revert α,
  rw [← is_almost_hermitian_iff_smul],
  apply is_almost_hermitian.of_inner_aut,
  exact hy.is_almost_hermitian,
end

/-- we say a matrix $x$ _has almost equal spectra to_ another matrix $y$ if
  there exists some scalar $0\neq\beta \in \mathbb{C}$ such that $x$ and $\beta y$ have equal spectra -/
def is_almost_hermitian.has_almost_equal_spectra_to
  {x y : matrix n n 𝕜} (hx : x.is_almost_hermitian) (hy : y.is_almost_hermitian) : Prop :=
∃ β : 𝕜ˣ, hx.spectra = (hy.smul β).spectra

end matrix
