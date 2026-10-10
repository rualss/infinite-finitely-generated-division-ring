import FRD.Defs
import FRD.Words.Basic
import FRD.Words.Free

namespace FRD

theorem WordBasis.nontrivial {B X R : Type*} [DivisionRing B] [Ring R] (wb : WordBasis B X R) :
    Nontrivial R := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h1 : wb.coeff (wb.ι 1) [] = 0 := by
    rw [map_one, h, map_zero, Finsupp.zero_apply]
  rw [wb.coeff_ι, Finsupp.single_eq_same] at h1
  exact one_ne_zero h1

theorem WordBasis.exists_depReducing {B X R : Type*} [DivisionRing B] [Ring R]
    (wb : WordBasis B X R) : ∃ μ : R → ℕ, DepReducing R μ :=
  ⟨wb.size, wb.depReducing⟩

theorem exists_wordBasis_freeAlgebra (k : Type) [Field k] (X : Type) :
    Nonempty (WordBasis k X (FreeAlgebra k X)) :=
  ⟨freeAlgebraWordBasis k X⟩

end FRD
