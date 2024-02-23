import linear_algebra.my_matrix.basic

namespace matrix

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n] [decidable_eq 𝕜]

open_locale matrix

noncomputable def is_hermitian.spectra {A : matrix n n 𝕜} (hA : A.is_hermitian) : multiset ℝ :=
finset.univ.val.map (λ i, hA.eigenvalues i)

end matrix
