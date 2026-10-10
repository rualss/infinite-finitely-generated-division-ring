import FRD.Loc.Universal

namespace FRD

theorem exists_universalLoc (R : Type) [Ring R] [IsSylvesterDomain R] :
    ∃ (K : Type) (_ : DivisionRing K) (ι : R →+* K), IsUniversalLoc ι :=
  ⟨Loc R, Loc.instDivisionRing, Loc.of,
    { injective := Loc.of_injective
      isUnit_map := fun _ A hA => Loc.isUnit_map_of A hA
      exists_lift := fun _ _ f hf =>
        ⟨Loc.liftHom f (inverts_of_fin f hf), Loc.liftHom_comp_of f _⟩
      hom_ext := fun _ _ g₁ g₂ h => Loc.hom_ext' g₁ g₂ h }⟩

end FRD
