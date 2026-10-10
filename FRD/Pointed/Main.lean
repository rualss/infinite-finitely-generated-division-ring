import FRD.Pointed.Ring

namespace FRD

theorem exists_wordBasis_of_pointed_bimodule (B : Type) [DivisionRing B] (M : Type)
    [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M] (one : M)
    (hone : ∀ c : B, c • one = MulOpposite.op c • one) (hne : one ≠ 0) :
    ∃ (X : Type) (R : Type) (_ : Ring R) (wb : WordBasis B X R) (j : M →+ R),
      j one = 1 ∧ (∀ (c : B) (m : M), j (c • m) = wb.ι c * j m) ∧
      (∀ (c : B) (m : M), j (MulOpposite.op c • m) = j m * wb.ι c) := by
  obtain ⟨X, b, hb⟩ := Pointed.exists_basis_option Bᵐᵒᵖ one hne
  have hone' : ∀ c : B, c • b none = MulOpposite.op c • b none := by
    intro c; rw [hb]; exact hone c
  refine ⟨X, Pointed.PRing b hone', inferInstance, Pointed.wordBasis b hone',
    Pointed.jHom b hone', ?_, ?_, ?_⟩
  · rw [← hb]; exact Pointed.jHom_one b hone'
  · exact fun c m => Pointed.jHom_left b hone' c m
  · exact fun c m => Pointed.jHom_right b hone' c m

end FRD
