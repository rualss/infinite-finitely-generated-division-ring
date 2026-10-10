import FRD.Defs

open scoped TensorProduct
open MulOpposite

namespace FRD

namespace FreeField

set_option maxSynthPendingDepth 6

theorem isUnit_of_isUnit_map_of_sqZero {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (s : B → A)
    (hfs : ∀ y, f (s y) = y) (hker : ∀ x y, f x = 0 → f y = 0 → x * y = 0) (x : A)
    (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  have hfp : f (s (↑u⁻¹ : B)) = ↑u⁻¹ := hfs _
  generalize s (↑u⁻¹ : B) = p at hfp
  have h1 : f (1 - x * p) = 0 := by
    rw [map_sub, map_one, map_mul, hfp, ← hu, Units.mul_inv, sub_self]
  have h2 : f (1 - p * x) = 0 := by
    rw [map_sub, map_one, map_mul, hfp, ← hu, Units.inv_mul, sub_self]
  have e1 : (1 - x * p) * (1 - x * p) = 0 := hker _ _ h1 h1
  have e2 : (1 - p * x) * (1 - p * x) = 0 := hker _ _ h2 h2
  refine isUnit_iff_exists_and_exists.mpr
    ⟨⟨p * (1 + (1 - x * p)), ?_⟩, ⟨(1 + (1 - p * x)) * p, ?_⟩⟩
  · have : x * (p * (1 + (1 - x * p))) = 1 - (1 - x * p) * (1 - x * p) := by noncomm_ring
    rw [this, e1, sub_zero]
  · have : (1 + (1 - p * x)) * p * x = 1 - (1 - p * x) * (1 - p * x) := by noncomm_ring
    rw [this, e2, sub_zero]

theorem ringHom_ext_freeAlgebra {X : Type*} {A : Type*} [Semiring A]
    (f g : FreeAlgebra (ZMod 2) X →+* A)
    (h : ∀ x, f (FreeAlgebra.ι (ZMod 2) x) = g (FreeAlgebra.ι (ZMod 2) x)) : f = g := by
  refine RingHom.ext fun p => ?_
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    exact congrArg (fun k : ZMod 2 →+* A => k r)
      (RingHom.ext_zmod (f.comp (algebraMap (ZMod 2) (FreeAlgebra (ZMod 2) X)))
        (g.comp (algebraMap (ZMod 2) (FreeAlgebra (ZMod 2) X))))
  | grade1 x => exact h x
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem tsze_mul_eq_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    (x y : TrivSqZeroExt R M) (hx : x.fst = 0) (hy : y.fst = 0) : x * y = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, hx, zero_mul, TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, hx, hy, zero_smul, op_zero, zero_smul, add_zero,
      TrivSqZeroExt.snd_zero]

theorem tsze_matrix_isUnit {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (TrivSqZeroExt R M)) (h : IsUnit (N.map TrivSqZeroExt.fst)) : IsUnit N := by
  let π : TrivSqZeroExt R M →+* R := (TrivSqZeroExt.fstHom ℕ R M : TrivSqZeroExt R M →+* R)
  refine isUnit_of_isUnit_map_of_sqZero (RingHom.mapMatrix π)
    (fun Θ => Θ.map (TrivSqZeroExt.inl : R → TrivSqZeroExt R M)) ?_ ?_ N h
  · intro Θ
    refine Matrix.ext fun i j => ?_
    simp [π]
  · intro X Y hX hY
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    apply tsze_mul_eq_zero
    · simpa [π] using congrFun (congrFun hX i) k
    · simpa [π] using congrFun (congrFun hY k) j

section Bimodule

variable (K : Type) [Ring K] [Algebra (ZMod 2) K]

def Bim : Type := Env K × Env K

noncomputable instance : AddCommGroup (Bim K) :=
  inferInstanceAs (AddCommGroup (Env K × Env K))

noncomputable instance : Module (Env K) (Bim K) :=
  inferInstanceAs (Module (Env K) (Env K × Env K))

noncomputable instance : Module (ZMod 2) (Bim K) :=
  inferInstanceAs (Module (ZMod 2) (Env K × Env K))

instance : IsScalarTower (ZMod 2) (Env K) (Bim K) :=
  inferInstanceAs (IsScalarTower (ZMod 2) (Env K) (Env K × Env K))

instance : SMulCommClass (Env K) (ZMod 2) (Bim K) :=
  inferInstanceAs (SMulCommClass (Env K) (ZMod 2) (Env K × Env K))

noncomputable instance : Module K (Bim K) :=
  Module.compHom (Bim K) (Algebra.TensorProduct.includeLeftRingHom : K →+* Env K)

noncomputable instance : Module Kᵐᵒᵖ (Bim K) :=
  Module.compHom (Bim K)
    ((Algebra.TensorProduct.includeRight : Kᵐᵒᵖ →ₐ[ZMod 2] Env K) : Kᵐᵒᵖ →+* Env K)

variable {K}

theorem smul_left_def (c : K) (m : Bim K) :
    c • m = (c ⊗ₜ[ZMod 2] (1 : Kᵐᵒᵖ) : Env K) • m := rfl

theorem smul_right_def (d : Kᵐᵒᵖ) (m : Bim K) :
    d • m = ((1 : K) ⊗ₜ[ZMod 2] d : Env K) • m := rfl

instance : SMulCommClass K Kᵐᵒᵖ (Bim K) where
  smul_comm c d m := by
    rw [smul_left_def, smul_right_def, smul_left_def, smul_right_def, smul_smul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      mul_one, one_mul]

instance : IsScalarTower (ZMod 2) K (Bim K) where
  smul_assoc z c m := by
    rw [smul_left_def, smul_left_def, ← TensorProduct.smul_tmul', smul_assoc]

instance : IsScalarTower (ZMod 2) Kᵐᵒᵖ (Bim K) where
  smul_assoc z d m := by
    rw [smul_right_def, smul_right_def, TensorProduct.tmul_smul, smul_assoc]

variable (K)

noncomputable def e0 : Bim K := ((1 : Env K), (0 : Env K))

noncomputable def e1 : Bim K := ((0 : Env K), (1 : Env K))

variable {K}

theorem smul_e0_add_smul_e1 (s t : Env K) (h : s • e0 K + t • e1 K = 0) : s = 0 ∧ t = 0 := by
  have h' : (s • ((1 : Env K), (0 : Env K)) + t • ((0 : Env K), (1 : Env K)) : Env K × Env K)
      = 0 := h
  simpa [Prod.ext_iff] using h'

end Bimodule

section Main

variable {K : Type} [Ring K] [Algebra (ZMod 2) K]

noncomputable def phi0 (a b : K) :
    FreeAlgebra (ZMod 2) (Fin 2) →ₐ[ZMod 2] TrivSqZeroExt K (Bim K) :=
  FreeAlgebra.lift (ZMod 2)
    ![TrivSqZeroExt.inl a + TrivSqZeroExt.inr (e0 K),
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (e1 K)]

theorem phi0_ι_zero (a b : K) :
    phi0 a b (FreeAlgebra.ι (ZMod 2) 0) = TrivSqZeroExt.inl a + TrivSqZeroExt.inr (e0 K) := by
  rw [phi0, FreeAlgebra.lift_ι_apply]
  rfl

theorem phi0_ι_one (a b : K) :
    phi0 a b (FreeAlgebra.ι (ZMod 2) 1) = TrivSqZeroExt.inl b + TrivSqZeroExt.inr (e1 K) := by
  rw [phi0, FreeAlgebra.lift_ι_apply]
  rfl

theorem fst_comp_phi0 (ι : FreeAlgebra (ZMod 2) (Fin 2) →+* K) :
    ((TrivSqZeroExt.fstHom (ZMod 2) K (Bim K) : TrivSqZeroExt K (Bim K) →+* K).comp
      (phi0 (ι (FreeAlgebra.ι (ZMod 2) 0)) (ι (FreeAlgebra.ι (ZMod 2) 1)) :
        FreeAlgebra (ZMod 2) (Fin 2) →+* TrivSqZeroExt K (Bim K))) = ι := by
  refine ringHom_ext_freeAlgebra _ _ fun x => ?_
  fin_cases x
  · simp [phi0_ι_zero]
  · simp [phi0_ι_one]

noncomputable def derivOf (g : K →+* TrivSqZeroExt K (Bim K)) : K →+ Bim K where
  toFun c := (g c).snd
  map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero]
  map_add' c d := by rw [map_add, TrivSqZeroExt.snd_add]

theorem derivOf_apply (g : K →+* TrivSqZeroExt K (Bim K)) (c : K) :
    derivOf g c = (g c).snd := rfl

theorem derivOf_mul (g : K →+* TrivSqZeroExt K (Bim K)) (hg : ∀ c, (g c).fst = c) (c d : K) :
    derivOf g (c * d) = c • derivOf g d + op d • derivOf g c := by
  rw [derivOf_apply, derivOf_apply, derivOf_apply, map_mul, TrivSqZeroExt.snd_mul, hg, hg]

noncomputable def Gmap (δ : K →+ Bim K) : Env K →+ Bim K :=
  TensorProduct.liftAddHom
    { toFun := fun u =>
        { toFun := fun v => (u ⊗ₜ[ZMod 2] (1 : Kᵐᵒᵖ) : Env K) • δ (unop v)
          map_zero' := by rw [unop_zero, map_zero, smul_zero]
          map_add' := fun v w => by rw [unop_add, map_add, smul_add] }
      map_zero' := by
        ext v
        simp
      map_add' := fun u u' => by
        ext v
        simp [TensorProduct.add_tmul, add_smul] }
    (fun r u v => by
      show ((r • u) ⊗ₜ[ZMod 2] (1 : Kᵐᵒᵖ) : Env K) • δ (unop v)
        = (u ⊗ₜ[ZMod 2] (1 : Kᵐᵒᵖ) : Env K) • δ (unop (r • v))
      rw [unop_smul, ZMod.map_smul, ← TensorProduct.smul_tmul', smul_assoc, smul_comm])

theorem Gmap_tmul (δ : K →+ Bim K) (u : K) (v : Kᵐᵒᵖ) :
    Gmap δ (u ⊗ₜ[ZMod 2] v) = (u ⊗ₜ[ZMod 2] (1 : Kᵐᵒᵖ) : Env K) • δ (unop v) := rfl

theorem Gmap_mul_kappa (δ : K →+ Bim K) (hδ : ∀ c d, δ (c * d) = c • δ d + op d • δ c)
    (e : Env K) (c : K) : Gmap δ (e * kappa c) = -(e • δ c) := by
  induction e using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_smul, neg_zero]
  | tmul u v =>
    rw [kappa, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      map_sub, Gmap_tmul, Gmap_tmul, mul_one, mul_one, unop_mul, unop_op, hδ, smul_left_def,
      smul_right_def, op_unop, smul_add, smul_smul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      mul_one]
    abel
  | add x y hx hy => rw [add_mul, map_add, hx, hy, add_smul, neg_add]

theorem kappa_linearIndependent (ι : FreeAlgebra (ZMod 2) (Fin 2) →+* K)
    (hι : IsUniversalLoc ι) :
    LinearIndependent (Env K)
      ![kappa (ι (FreeAlgebra.ι (ZMod 2) 0)), kappa (ι (FreeAlgebra.ι (ZMod 2) 1))] := by

  let φ : FreeAlgebra (ZMod 2) (Fin 2) →+* TrivSqZeroExt K (Bim K) :=
    (phi0 (ι (FreeAlgebra.ι (ZMod 2) 0)) (ι (FreeAlgebra.ι (ZMod 2) 1)) :
      FreeAlgebra (ZMod 2) (Fin 2) →+* TrivSqZeroExt K (Bim K))
  let π : TrivSqZeroExt K (Bim K) →+* K :=
    (TrivSqZeroExt.fstHom (ZMod 2) K (Bim K) : TrivSqZeroExt K (Bim K) →+* K)
  have hπφ : π.comp φ = ι := fst_comp_phi0 ι

  have hunit : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FreeAlgebra (ZMod 2) (Fin 2))),
      IsFull A → IsUnit (A.map φ) := by
    intro n A hA
    apply tsze_matrix_isUnit
    have h := hι.isUnit_map n A hA
    have e : (A.map φ).map TrivSqZeroExt.fst = A.map ι := by
      rw [Matrix.map_map]
      refine Matrix.ext fun i j => ?_
      exact RingHom.congr_fun hπφ (A i j)
    rw [e]
    exact h

  obtain ⟨g, hg⟩ := hι.exists_lift (TrivSqZeroExt K (Bim K)) φ hunit
  have hπg : π.comp g = RingHom.id K :=
    hι.hom_ext K _ _ (by rw [RingHom.comp_assoc, hg, hπφ, RingHom.id_comp])
  have hfst : ∀ c, (g c).fst = c := fun c => RingHom.congr_fun hπg c

  have hδa : derivOf g (ι (FreeAlgebra.ι (ZMod 2) 0)) = e0 K := by
    have h1 : g (ι (FreeAlgebra.ι (ZMod 2) 0)) = φ (FreeAlgebra.ι (ZMod 2) 0) :=
      RingHom.congr_fun hg _
    have h2 : φ (FreeAlgebra.ι (ZMod 2) 0) = TrivSqZeroExt.inl _ + TrivSqZeroExt.inr (e0 K) :=
      phi0_ι_zero _ _
    rw [derivOf_apply, h1, h2, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  have hδb : derivOf g (ι (FreeAlgebra.ι (ZMod 2) 1)) = e1 K := by
    have h1 : g (ι (FreeAlgebra.ι (ZMod 2) 1)) = φ (FreeAlgebra.ι (ZMod 2) 1) :=
      RingHom.congr_fun hg _
    have h2 : φ (FreeAlgebra.ι (ZMod 2) 1) = TrivSqZeroExt.inl _ + TrivSqZeroExt.inr (e1 K) :=
      phi0_ι_one _ _
    rw [derivOf_apply, h1, h2, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]

  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := congrArg (Gmap (derivOf g)) hst
  rw [smul_eq_mul, smul_eq_mul, map_add, Gmap_mul_kappa _ (derivOf_mul g hfst),
    Gmap_mul_kappa _ (derivOf_mul g hfst), map_zero, hδa, hδb, ← neg_add, neg_eq_zero] at h
  exact smul_e0_add_smul_e1 s t h

end Main

end FreeField

theorem kappa_linearIndependent_of_universalLoc {K : Type} [DivisionRing K] [Algebra (ZMod 2) K]
    (ι : FreeAlgebra (ZMod 2) (Fin 2) →+* K) (hι : IsUniversalLoc ι) :
    LinearIndependent (Env K)
      ![kappa (ι (FreeAlgebra.ι (ZMod 2) 0)), kappa (ι (FreeAlgebra.ι (ZMod 2) 1))] :=
  FreeField.kappa_linearIndependent ι hι

end FRD
