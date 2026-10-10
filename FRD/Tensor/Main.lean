import FRD.Defs

open scoped TensorProduct

namespace FRD

theorem exists_right_coords {F B : Type} [DivisionRing F] [DivisionRing B]
    [Algebra (ZMod 2) F] [Algebra (ZMod 2) B] (f : F →+* B) :
    ∃ (I : Type) (e : B ≃ₗ[ZMod 2] (I →₀ F)),
      ∀ (x : B) (s : F) (i : I), e (x * f s) i = e x i * s := by

  let _inst : Module Fᵐᵒᵖ B := Module.compHom B (RingHom.op f)
  let α := Module.Basis.ofVectorSpace Fᵐᵒᵖ B
  let e₀ : B ≃+ (Module.Basis.ofVectorSpaceIndex Fᵐᵒᵖ B →₀ F) :=
    α.repr.toAddEquiv.trans (Finsupp.mapRange.addEquiv MulOpposite.opAddEquiv.symm)
  refine ⟨_, { e₀ with map_smul' := fun c x => ZMod.map_smul e₀ c x }, ?_⟩
  intro x s i
  have hx : x * f s = MulOpposite.op s • x := rfl
  change e₀ (x * f s) i = e₀ x i * s
  rw [hx]
  simp [e₀]

section Abstract

variable {k : Type*} [CommRing k] {S₁ S₂ T₁ T₂ : Type*} [Ring S₁] [Ring S₂] [Ring T₁] [Ring T₂]
  [Algebra k S₁] [Algebra k S₂] [Algebra k T₁] [Algebra k T₂]
  (g₁ : S₁ →ₐ[k] T₁) (g₂ : S₂ →ₐ[k] T₂) {I J : Type*}
  (e₁ : T₁ ≃ₗ[k] (I →₀ S₁)) (e₂ : T₂ ≃ₗ[k] (J →₀ S₂))

noncomputable def coordMap (i : I) (l : J) : T₁ ⊗[k] T₂ →ₗ[k] S₁ ⊗[k] S₂ :=
  TensorProduct.map ((Finsupp.lapply i).comp e₁.toLinearMap)
    ((Finsupp.lapply l).comp e₂.toLinearMap)

@[simp] theorem coordMap_tmul (i : I) (l : J) (x : T₁) (y : T₂) :
    coordMap e₁ e₂ i l (x ⊗ₜ y) = e₁ x i ⊗ₜ e₂ y l := rfl

theorem coordMap_mul_map (h₁ : ∀ x s i, e₁ (x * g₁ s) i = e₁ x i * s)
    (h₂ : ∀ y s l, e₂ (y * g₂ s) l = e₂ y l * s) (i : I) (l : J)
    (w : T₁ ⊗[k] T₂) (e : S₁ ⊗[k] S₂) :
    coordMap e₁ e₂ i l (w * Algebra.TensorProduct.map g₁ g₂ e) = coordMap e₁ e₂ i l w * e := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ => simp [add_mul, hw₁, hw₂]
  | tmul x y =>
    induction e using TensorProduct.induction_on with
    | zero => simp
    | add e₁' e₂' he₁ he₂ => simp [mul_add, he₁, he₂]
    | tmul r s => simp [h₁, h₂]

theorem eq_zero_of_coordMap (w : T₁ ⊗[k] T₂) (hw : ∀ i l, coordMap e₁ e₂ i l w = 0) : w = 0 := by
  let Φ : T₁ ⊗[k] T₂ ≃ₗ[k] (I × J →₀ S₁ ⊗[k] S₂) :=
    (TensorProduct.congr e₁ e₂).trans (finsuppTensorFinsupp k k S₁ S₂ I J)
  have hΦ : ∀ (w : T₁ ⊗[k] T₂) (i : I) (l : J), Φ w (i, l) = coordMap e₁ e₂ i l w := by
    intro w i l
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul x y => simp [Φ]
  apply Φ.injective
  ext ⟨i, l⟩ : 1
  rw [hΦ, hw, map_zero, Finsupp.zero_apply]

theorem linearIndependent_map_of_coords (h₁ : ∀ x s i, e₁ (x * g₁ s) i = e₁ x i * s)
    (h₂ : ∀ y s l, e₂ (y * g₂ s) l = e₂ y l * s) {ι : Type*} (h : ι → S₁ ⊗[k] S₂)
    (hh : LinearIndependent (S₁ ⊗[k] S₂) h) :
    LinearIndependent (T₁ ⊗[k] T₂) (fun i => Algebra.TensorProduct.map g₁ g₂ (h i)) := by
  rw [linearIndependent_iff'] at hh ⊢
  intro s g hg n hn
  apply eq_zero_of_coordMap e₁ e₂
  intro i l
  have := congrArg (coordMap e₁ e₂ i l) hg
  rw [map_sum, map_zero] at this
  simp only [smul_eq_mul, coordMap_mul_map g₁ g₂ e₁ e₂ h₁ h₂] at this
  exact hh s (fun n => coordMap e₁ e₂ i l (g n)) this n hn

end Abstract

theorem linearIndependent_envMap {F B : Type} [DivisionRing F] [DivisionRing B]
    [Algebra (ZMod 2) F] [Algebra (ZMod 2) B] (f : F →ₐ[ZMod 2] B) {ι : Type} (h : ι → Env F)
    (hh : LinearIndependent (Env F) h) : LinearIndependent (Env B) (fun i => envMap f (h i)) := by
  obtain ⟨I, e₁, h₁⟩ := exists_right_coords (f : F →+* B)
  obtain ⟨J, e₂, h₂⟩ :=
    exists_right_coords ((AlgHom.op f : Fᵐᵒᵖ →ₐ[ZMod 2] Bᵐᵒᵖ) : Fᵐᵒᵖ →+* Bᵐᵒᵖ)
  exact linearIndependent_map_of_coords f (AlgHom.op f) e₁ e₂ h₁ h₂ h hh

theorem envMap_kappa {F B : Type*} [Ring F] [Ring B] [Algebra (ZMod 2) F] [Algebra (ZMod 2) B]
    (f : F →ₐ[ZMod 2] B) (c : F) : envMap f (kappa c) = kappa (f c) := by
  simp [envMap, kappa]

theorem kappa_pow_aux {A : Type*} [Ring A] [Algebra (ZMod 2) A] (a b : A)
    (h : LinearIndependent (Env A) ![kappa a, kappa b]) :
    ∀ (N : ℕ) (g : ℕ → Env A),
      ∑ j ∈ Finset.range N, g j * (kappa b * kappa a ^ j) = 0 → ∀ j < N, g j = 0 := by
  rw [LinearIndependent.pair_iff] at h
  intro N
  induction N with
  | zero => intro g _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ N ih =>
    intro g hg
    rw [Finset.sum_range_succ'] at hg
    have key : (∑ j ∈ Finset.range N, g (j + 1) * (kappa b * kappa a ^ j)) • kappa a
        + g 0 • kappa b = 0 := by
      rw [← hg, smul_eq_mul, smul_eq_mul, Finset.sum_mul, pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ, mul_assoc, mul_assoc]
    obtain ⟨h1, h0⟩ := h _ _ key
    have ih' := ih (fun j => g (j + 1)) h1
    intro j hj
    cases j with
    | zero => exact h0
    | succ j => exact ih' j (Nat.lt_of_succ_lt_succ hj)

theorem kappa_pow_linearIndependent {A : Type*} [Ring A] [Algebra (ZMod 2) A] (a b : A)
    (h : LinearIndependent (Env A) ![kappa a, kappa b]) :
    LinearIndependent (Env A) (fun j : ℕ => kappa b * kappa a ^ j) := by
  classical
  rw [linearIndependent_iff'']
  intro s g hgs hsum j
  obtain ⟨N, hN⟩ := s.exists_nat_subset_range
  have hsum' : ∑ j ∈ Finset.range N, g j * (kappa b * kappa a ^ j) = 0 := by
    rw [← hsum]
    symm
    refine Finset.sum_subset hN fun i _ hi => ?_
    rw [hgs i hi, zero_smul]
  by_cases hj : j ∈ s
  · exact kappa_pow_aux a b h N g hsum' j (Finset.mem_range.mp (hN hj))
  · exact hgs j hj

namespace PointedBimodule

variable {B : Type} [DivisionRing B] [Algebra (ZMod 2) B]

noncomputable local instance envModule : Module (Env B) B := TensorProduct.Algebra.module

theorem env_smul_def (u : B) (v : Bᵐᵒᵖ) (x : B) :
    (u ⊗ₜ[ZMod 2] v : Env B) • x = u * x * v.unop := by
  rw [TensorProduct.Algebra.smul_def]
  induction v using MulOpposite.rec'
  simp [mul_assoc]

variable (a b : B) (d : ℕ → B)

noncomputable def rel : Submodule (Env B) (B × Env B) :=
  Submodule.span (Env B) (Set.range fun j : ℕ => ((-(d j), kappa b * kappa a ^ j) : B × Env B))

def PB : Type := (B × Env B) ⧸ rel a b d

noncomputable instance : AddCommGroup (PB a b d) :=
  inferInstanceAs (AddCommGroup ((B × Env B) ⧸ rel a b d))

noncomputable instance : Module (Env B) (PB a b d) :=
  inferInstanceAs (Module (Env B) ((B × Env B) ⧸ rel a b d))

noncomputable instance : Module B (PB a b d) :=
  Module.compHom _ (Algebra.TensorProduct.includeLeftRingHom : B →+* Env B)

noncomputable instance : Module Bᵐᵒᵖ (PB a b d) :=
  Module.compHom _ ((Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[ZMod 2] Env B) : Bᵐᵒᵖ →+* Env B)

variable {a b d}

theorem smul_left_def (c : B) (m : PB a b d) :
    c • m = (c ⊗ₜ[ZMod 2] (1 : Bᵐᵒᵖ) : Env B) • m := rfl

theorem smul_right_def (c : Bᵐᵒᵖ) (m : PB a b d) :
    c • m = ((1 : B) ⊗ₜ[ZMod 2] c : Env B) • m := rfl

instance : SMulCommClass B Bᵐᵒᵖ (PB a b d) :=
  ⟨fun c c' m => by
    rw [smul_right_def, smul_left_def, smul_left_def, smul_right_def, ← mul_smul, ← mul_smul]
    simp⟩

variable (a b d) in

noncomputable def mk : B × Env B →ₗ[Env B] PB a b d := (rel a b d).mkQ

theorem mk_eq_zero_iff (x : B × Env B) : mk a b d x = 0 ↔ x ∈ rel a b d :=
  Submodule.Quotient.mk_eq_zero _

theorem adBim_eq (c : B) (m : PB a b d) : adBim c m = kappa c • m := by
  rw [adBim, kappa, sub_smul, smul_left_def, smul_right_def]

theorem adBim_iterate (c : B) (j : ℕ) (m : PB a b d) : (adBim c)^[j] m = kappa c ^ j • m := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, adBim_eq, ← mul_smul, pow_succ']

theorem KopBim_eq (j : ℕ) (m : PB a b d) : KopBim a b j m = (kappa b * kappa a ^ j) • m := by
  rw [KopBim, adBim_iterate, adBim_eq, mul_smul]

theorem smul_one_left (c : B) : c • mk a b d (1, 0) = mk a b d (c, 0) := by
  rw [smul_left_def, ← map_smul, Prod.smul_mk, smul_zero, env_smul_def]
  simp

theorem smul_one_right (c : B) : MulOpposite.op c • mk a b d (1, 0) = mk a b d (c, 0) := by
  rw [smul_right_def, ← map_smul, Prod.smul_mk, smul_zero, env_smul_def]
  simp

theorem KopBim_m₀ (j : ℕ) : KopBim a b j (mk a b d (0, 1)) = d j • mk a b d (1, 0) := by
  rw [KopBim_eq, smul_one_left, ← map_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
    ← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  refine Submodule.subset_span ⟨j, ?_⟩
  simp

theorem mk_one_ne_zero (h : LinearIndependent (Env B) (fun j : ℕ => kappa b * kappa a ^ j)) :
    mk a b d (1, 0) ≠ 0 := by
  rw [Ne, mk_eq_zero_iff, rel, Finsupp.mem_span_range_iff_exists_finsupp]
  rintro ⟨c, hc⟩
  have h2 := congrArg (LinearMap.snd (Env B) B (Env B)) hc
  rw [map_finsuppSum] at h2
  have hc0 : c = 0 := by
    apply linearIndependent_iff.mp h
    rw [Finsupp.linearCombination_apply]
    simpa using h2
  rw [hc0, Finsupp.sum_zero_index] at hc
  exact one_ne_zero (congrArg Prod.fst hc).symm

end PointedBimodule

open PointedBimodule in

theorem exists_pointed_bimodule {B : Type} [DivisionRing B] [Algebra (ZMod 2) B] (a b : B)
    (d : ℕ → B) (h : LinearIndependent (Env B) (fun j : ℕ => kappa b * kappa a ^ j)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module B M) (_ : Module Bᵐᵒᵖ M)
      (_ : SMulCommClass B Bᵐᵒᵖ M) (one m₀ : M),
      (∀ c : B, c • one = MulOpposite.op c • one) ∧ one ≠ 0 ∧
      ∀ j, KopBim a b j m₀ = d j • one :=
  ⟨PB a b d, inferInstance, inferInstance, inferInstance, inferInstance,
    mk a b d (1, 0), mk a b d (0, 1),
    fun c => by rw [smul_one_left, smul_one_right], mk_one_ne_zero h, KopBim_m₀⟩

end FRD
