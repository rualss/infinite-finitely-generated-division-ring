import FRD.Loc.Main
import FRD.Sylvester.Main
import FRD.Words.Main
import FRD.Pointed.Main
import FRD.Tensor.Main
import FRD.FreeField.Main

namespace FRD

theorem map_Kop {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) (j : ℕ) (v : R) :
    f (Kop a b j v) = Kop (f a) (f b) j (f v) := by
  have h : ∀ w, f ((fun w => a * w - w * a)^[j] w) = (fun w => f a * w - w * f a)^[j] (f w) := by
    induction j with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      simp
  simp only [Kop, map_sub, map_mul, h]

theorem map_KopBim {B M R : Type*} [Ring B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [Ring R] (ι : B →+* R) (j : M →+ R) (hl : ∀ (c : B) (m : M), j (c • m) = ι c * j m)
    (hr : ∀ (c : B) (m : M), j (MulOpposite.op c • m) = j m * ι c) (a b : B) (n : ℕ) (m : M) :
    j (KopBim a b n m) = Kop (ι a) (ι b) n (j m) := by
  have had : ∀ (c : B) (m : M), j (adBim c m) = ι c * j m - j m * ι c := by
    intro c m; simp [adBim, hl, hr]
  have h : ∀ m, j ((adBim a)^[n] m) = (fun w => ι a * w - w * ι a)^[n] (j m) := by
    induction n with
    | zero => intro m; rfl
    | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, had]
  simp only [KopBim, Kop, had, h]

theorem frd1 : FRD1 := by
  classical

  obtain ⟨wb₀⟩ := exists_wordBasis_freeAlgebra (ZMod 2) (Fin 2)
  haveI : Nontrivial (FreeAlgebra (ZMod 2) (Fin 2)) := wb₀.nontrivial
  obtain ⟨μ₀, hμ₀⟩ := wb₀.exists_depReducing
  haveI : IsSylvesterDomain (FreeAlgebra (ZMod 2) (Fin 2)) := hμ₀.isSylvesterDomain

  obtain ⟨K, _, ι, hι⟩ := exists_universalLoc (FreeAlgebra (ZMod 2) (Fin 2))
  haveI : CharP (FreeAlgebra (ZMod 2) (Fin 2)) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (FreeAlgebra (ZMod 2) (Fin 2))).injective 2
  haveI : CharP K 2 := charP_of_injective_ringHom hι.injective 2
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hind := kappa_linearIndependent_of_universalLoc ι hι
  refine ⟨K, inferInstance, inferInstance, ι (FreeAlgebra.ι (ZMod 2) 0),
    ι (FreeAlgebra.ι (ZMod 2) 1), ?_⟩
  intro B _ i d
  haveI : CharP B 2 := charP_of_injective_ringHom i.injective 2
  letI : Algebra (ZMod 2) B := ZMod.algebra B 2

  have hcomm : ∀ r : ZMod 2, i (algebraMap (ZMod 2) K r) = algebraMap (ZMod 2) B r :=
    fun r => RingHom.congr_fun
      (Subsingleton.elim (i.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) B)) r
  let f : K →ₐ[ZMod 2] B := { i with commutes' := hcomm }
  have h1 := linearIndependent_envMap f _ hind
  have h2 : LinearIndependent (Env B)
      ![kappa (i (ι (FreeAlgebra.ι (ZMod 2) 0))), kappa (i (ι (FreeAlgebra.ι (ZMod 2) 1)))] := by
    convert h1 using 1
    ext k
    fin_cases k <;> simp [envMap_kappa, f]
  have h3 := kappa_pow_linearIndependent _ _ h2

  obtain ⟨M, _, _, _, _, one, m₀, hone, hne, hK⟩ := exists_pointed_bimodule _ _ d h3
  obtain ⟨X, R, _, wb, j, hj1, hjl, hjr⟩ :=
    exists_wordBasis_of_pointed_bimodule B M one hone hne
  haveI : Nontrivial R := wb.nontrivial
  obtain ⟨μ, hμ⟩ := wb.exists_depReducing
  haveI : IsSylvesterDomain R := hμ.isSylvesterDomain
  obtain ⟨B', _, ι', hι'⟩ := exists_universalLoc R
  refine ⟨B', inferInstance, ι'.comp wb.ι, ι' (j m₀), fun n => ?_⟩
  have := congrArg ι' (map_KopBim wb.ι j hjl hjr (i (ι (FreeAlgebra.ι (ZMod 2) 0)))
    (i (ι (FreeAlgebra.ι (ZMod 2) 1))) n m₀)
  rw [map_Kop, hK n, hjl, hj1, mul_one] at this
  exact this.symm

end FRD
