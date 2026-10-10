import FRD.Defs

namespace FRD

noncomputable def freeAlgebraWordBasis (k : Type) [Field k] (X : Type) :
    WordBasis k X (FreeAlgebra k X) :=
  let e : FreeAlgebra k X ≃ₐ[k] MonoidAlgebra k (FreeMonoid X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
  have halg : ∀ c : k,
      algebraMap k (MonoidAlgebra k (FreeMonoid X)) c = MonoidAlgebra.single 1 c :=
    fun _ => rfl
  { ι := algebraMap k (FreeAlgebra k X)
    word := fun w => e.symm (MonoidAlgebra.of k (FreeMonoid X) (FreeMonoid.ofList w))
    coeff :=
      { toFun := fun r => (e r).coeff
        map_zero' := by rw [map_zero]; rfl
        map_add' := fun x y => by rw [map_add]; rfl }
    word_nil := by
      rw [FreeMonoid.ofList_nil, map_one, map_one]
    word_append := fun u v => by
      rw [FreeMonoid.ofList_append, map_mul, map_mul]
    coeff_injective := fun a b h => e.injective (MonoidAlgebra.coeff_injective h)
    coeff_ι := fun c => by
      change (e (algebraMap k (FreeAlgebra k X) c)).coeff = _
      rw [AlgEquiv.commutes, halg]
      rfl
    coeff_word_mul := fun u r w => by
      change (e (e.symm (MonoidAlgebra.of k (FreeMonoid X) (FreeMonoid.ofList u)) * r)).coeff
        (FreeMonoid.ofList u * FreeMonoid.ofList w) = (e r).coeff (FreeMonoid.ofList w)
      rw [map_mul e, AlgEquiv.apply_symm_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.coeff_single_mul_mul, one_mul]
    coeff_word_mul_of_not_prefix := fun u r w h => by
      change (e (e.symm (MonoidAlgebra.of k (FreeMonoid X) (FreeMonoid.ofList u)) * r)).coeff
        (FreeMonoid.ofList w) = 0
      rw [map_mul e, AlgEquiv.apply_symm_apply, MonoidAlgebra.of_apply]
      apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
      intro d hd
      exact h ⟨FreeMonoid.toList d, hd⟩
    coeff_mul_ι := fun r c w => by
      change (e (r * algebraMap k (FreeAlgebra k X) c)).coeff (FreeMonoid.ofList w)
        = (e r).coeff (FreeMonoid.ofList w) * c
      rw [map_mul e, AlgEquiv.commutes, halg, MonoidAlgebra.coeff_mul_single_one]
    filtration := fun c u w h => by
      change (e (algebraMap k (FreeAlgebra k X) c
        * e.symm (MonoidAlgebra.of k (FreeMonoid X) (FreeMonoid.ofList u)))).coeff
        (FreeMonoid.ofList w) ≠ 0 at h
      rw [map_mul e, AlgEquiv.commutes, AlgEquiv.apply_symm_apply, halg, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.coeff_single,
        Finsupp.single_apply_ne_zero] at h
      have h1 : w = u := h.1
      rw [h1] }

end FRD
