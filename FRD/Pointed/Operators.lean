import FRD.Defs

namespace FRD.Pointed

open MulOpposite

abbrev NF (B X : Type*) [Ring B] : Type _ := List X →₀ Bᵐᵒᵖ

abbrev Op (B X : Type*) [Ring B] : Type _ := Module.End Bᵐᵒᵖ (NF B X)

section Prepend

variable {B : Type*} [Ring B] {X : Type*}

theorem Op_ext {φ ψ : Op B X}
    (h : ∀ w : List X, φ (Finsupp.single w 1) = ψ (Finsupp.single w 1)) : φ = ψ := by
  refine Finsupp.lhom_ext fun w k => ?_
  have hk : (Finsupp.single w k : NF B X) = k • Finsupp.single w 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hk, map_smul, map_smul, h]

variable (B) in

noncomputable def Pw (w : List X) : Op B X :=
  Finsupp.lmapDomain Bᵐᵒᵖ Bᵐᵒᵖ (w ++ ·)

theorem Pw_apply (w : List X) (g : NF B X) : Pw B w g = Finsupp.mapDomain (w ++ ·) g := rfl

@[simp]
theorem Pw_single (u v : List X) (k : Bᵐᵒᵖ) :
    Pw B u (Finsupp.single v k) = Finsupp.single (u ++ v) k := by
  rw [Pw_apply, Finsupp.mapDomain_single]

@[simp]
theorem Pw_nil : Pw B ([] : List X) = 1 :=
  Op_ext fun w => by simp

theorem Pw_append (u v : List X) : Pw B (u ++ v) = Pw B u * Pw B v :=
  Op_ext fun w => by simp [Module.End.mul_apply]

theorem Pw_cons (x : X) (v : List X) : Pw B (x :: v) = Pw B [x] * Pw B v :=
  Pw_append [x] v

end Prepend

section Construction

variable {B : Type*} [Ring B] {X : Type*} {M : Type*} [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] (b : Module.Basis (Option X) Bᵐᵒᵖ M)

noncomputable def Lam : List X → B →+ NF B X
  | [] => (Finsupp.singleAddHom []).comp (opAddEquiv : B ≃+ Bᵐᵒᵖ).toAddMonoidHom
  | x :: v =>
    (Finsupp.liftAddHom fun o : Option X =>
        (Pw B o.toList : NF B X →ₗ[Bᵐᵒᵖ] NF B X).toAddMonoidHom.comp
          ((Lam v).comp (opAddEquiv : B ≃+ Bᵐᵒᵖ).symm.toAddMonoidHom)).comp
      (b.repr.toLinearMap.toAddMonoidHom.comp ((smulAddHom B M).flip (b (some x))))

theorem Lam_nil (a : B) : Lam b [] a = Finsupp.single [] (op a) := rfl

theorem Lam_cons (x : X) (v : List X) (a : B) :
    Lam b (x :: v) a =
      (b.repr (a • b (some x))).sum fun o k => Pw B o.toList (Lam b v (unop k)) := rfl

noncomputable def Lop : B →+ Op B X where
  toFun a := Finsupp.linearCombination Bᵐᵒᵖ fun w => Lam b w a
  map_zero' := Op_ext fun w => by simp
  map_add' a a' := Op_ext fun w => by simp

theorem Lop_single (a : B) (w : List X) (k : Bᵐᵒᵖ) :
    Lop b a (Finsupp.single w k) = k • Lam b w a := by
  simp [Lop]

@[simp]
theorem Lop_single_one (a : B) (w : List X) : Lop b a (Finsupp.single w 1) = Lam b w a := by
  rw [Lop_single, one_smul]

theorem Lop_single_nil (a : B) (k : Bᵐᵒᵖ) :
    Lop b a (Finsupp.single [] k) = Finsupp.single [] (k * op a) := by
  rw [Lop_single, Lam_nil, Finsupp.smul_single, smul_eq_mul]

noncomputable def ell : NF B X →+ Op B X :=
  Finsupp.liftAddHom fun w : List X =>
    (AddMonoidHom.mulLeft (Pw B w)).comp
      ((Lop b).comp (opAddEquiv : B ≃+ Bᵐᵒᵖ).symm.toAddMonoidHom)

@[simp]
theorem ell_single (w : List X) (k : Bᵐᵒᵖ) :
    ell b (Finsupp.single w k) = Pw B w * Lop b (unop k) := by
  simp [ell]

theorem ell_apply_nil (g : NF B X) : ell b g (Finsupp.single [] 1) = g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂]
  | single w k => simp [Module.End.mul_apply, Lam_nil]

theorem Pw_mul_ell (u : List X) (g : NF B X) : Pw B u * ell b g = ell b (Pw B u g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, map_add, map_add]
  | single w k => simp [Pw_append, mul_assoc]

noncomputable def emb : M →ₗ[Bᵐᵒᵖ] NF B X :=
  (Finsupp.lmapDomain Bᵐᵒᵖ Bᵐᵒᵖ Option.toList).comp b.repr.toLinearMap

omit [Module B M] in
theorem emb_apply (m : M) : emb b m = Finsupp.mapDomain Option.toList (b.repr m) := rfl

noncomputable def J : M →+ Op B X := (ell b).comp (emb b).toAddMonoidHom

theorem J_apply (m : M) : J b m = ell b (emb b m) := rfl

theorem J_smul_basis (o : Option X) (k : Bᵐᵒᵖ) :
    J b (k • b o) = Pw B o.toList * Lop b (unop k) := by
  simp [J_apply, emb_apply]

theorem ell_mapDomain_apply_single (γ : Option X →₀ Bᵐᵒᵖ) (v : List X) :
    ell b (Finsupp.mapDomain Option.toList γ) (Finsupp.single v 1) =
      γ.sum fun o k => Pw B o.toList (Lam b v (unop k)) := by
  induction γ using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ =>
    rw [Finsupp.mapDomain_add, map_add, LinearMap.add_apply, h₁, h₂, Finsupp.sum_add_index']
    · intro o; simp
    · intro o k k'; simp
  | single o k => simp [Module.End.mul_apply]

theorem J_apply_single (m : M) (v : List X) :
    J b m (Finsupp.single v 1) =
      (b.repr m).sum fun o k => Pw B o.toList (Lam b v (unop k)) :=
  ell_mapDomain_apply_single b _ v

theorem Lop_mul_Pw_some (a : B) (x : X) : Lop b a * Pw B [x] = J b (a • b (some x)) :=
  Op_ext fun v => by
    rw [Module.End.mul_apply, Pw_single, J_apply_single, List.singleton_append, Lop_single_one,
      Lam_cons]

theorem Lam_one (w : List X) : Lam b w 1 = Finsupp.single w 1 := by
  induction w with
  | nil => simp [Lam_nil]
  | cons x v ih => simp [Lam_cons, ih]

@[simp]
theorem Lop_one : Lop b 1 = 1 :=
  Op_ext fun w => by simp [Lam_one]

@[simp]
theorem ell_single_one (w : List X) : ell b (Finsupp.single w 1) = Pw B w := by
  simp

theorem J_basis (o : Option X) : J b (b o) = Pw B o.toList := by
  simpa using J_smul_basis b o 1

end Construction

section Multiplicativity

variable {B : Type*} [Ring B] {X : Type*} {M : Type*} [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M] (b : Module.Basis (Option X) Bᵐᵒᵖ M)

omit [SMulCommClass B Bᵐᵒᵖ M] in

theorem ell_smul_apply_of (z : NF B X)
    (h : ∀ a a' : B, Lop b (a * a') z = Lop b a (Lop b a' z)) (k : Bᵐᵒᵖ) (g : NF B X) :
    ell b (k • g) z = ell b g (Lop b (unop k) z) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => rw [smul_add, map_add, map_add, LinearMap.add_apply, h₁, h₂,
      LinearMap.add_apply]
  | single w k' =>
    rw [Finsupp.smul_single, smul_eq_mul, ell_single, ell_single, Module.End.mul_apply,
      Module.End.mul_apply, unop_mul, h]

omit [SMulCommClass B Bᵐᵒᵖ M] in
theorem J_smul_apply_of (z : NF B X)
    (h : ∀ a a' : B, Lop b (a * a') z = Lop b a (Lop b a' z)) (k : Bᵐᵒᵖ) (m : M) :
    J b (k • m) z = J b m (Lop b (unop k) z) := by
  rw [J_apply, map_smul, ell_smul_apply_of b z h, J_apply]

variable (hone : ∀ c : B, c • b none = op c • b none)
include hone

omit [SMulCommClass B Bᵐᵒᵖ M] in

theorem Lop_mul_Pw_toList (a : B) (o : Option X) :
    Lop b a * Pw B o.toList = J b (a • b o) := by
  cases o with
  | none => rw [hone, J_smul_basis]; simp
  | some x => exact Lop_mul_Pw_some b a x

theorem J_left_apply_of (z : NF B X)
    (h : ∀ a a' : B, Lop b (a * a') z = Lop b a (Lop b a' z)) (a : B) (m : M) :
    J b (a • m) z = Lop b a (J b m z) := by
  have key : ∀ f : Option X →₀ Bᵐᵒᵖ,
      J b (a • b.repr.symm f) z = Lop b a (J b (b.repr.symm f) z) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => rw [map_add, smul_add, map_add, map_add, LinearMap.add_apply, h₁, h₂,
        LinearMap.add_apply, map_add]
    | single o k =>
      rw [Module.Basis.repr_symm_single, smul_comm a k (b o), J_smul_apply_of b z h,
        J_smul_apply_of b z h, ← Lop_mul_Pw_toList b hone, J_basis, Module.End.mul_apply]
  simpa using key (b.repr m)

theorem Lop_mul_apply_single (w : List X) :
    ∀ a a' : B, Lop b (a * a') (Finsupp.single w 1) =
      Lop b a (Lop b a' (Finsupp.single w 1)) := by
  induction w with
  | nil =>
    intro a a'
    rw [Lop_single_one, Lop_single_one, Lam_nil, Lam_nil, Lop_single_nil, op_mul]
  | cons x v ih =>
    intro a a'
    have hx : (Finsupp.single (x :: v) 1 : NF B X) = Pw B [x] (Finsupp.single v 1) := by simp
    rw [hx, ← Module.End.mul_apply, ← Module.End.mul_apply (Lop b a'), Lop_mul_Pw_some,
      Lop_mul_Pw_some, mul_smul, J_left_apply_of b hone _ ih]

theorem Lop_mul (a a' : B) : Lop b (a * a') = Lop b a * Lop b a' :=
  Op_ext fun w => Lop_mul_apply_single b hone w a a'

theorem Lop_mul_apply (a a' : B) (z : NF B X) : Lop b (a * a') z = Lop b a (Lop b a' z) := by
  rw [Lop_mul b hone, Module.End.mul_apply]

noncomputable def LopHom : B →+* Op B X :=
  { Lop b with
    map_one' := Lop_one b
    map_mul' := Lop_mul b hone }

@[simp]
theorem LopHom_apply (a : B) : LopHom b hone a = Lop b a := rfl

theorem ell_smul (k : Bᵐᵒᵖ) (g : NF B X) : ell b (k • g) = ell b g * Lop b (unop k) :=
  LinearMap.ext fun z => ell_smul_apply_of b z (fun a a' => Lop_mul_apply b hone a a' z) k g

theorem J_smul (k : Bᵐᵒᵖ) (m : M) : J b (k • m) = J b m * Lop b (unop k) :=
  LinearMap.ext fun z => J_smul_apply_of b z (fun a a' => Lop_mul_apply b hone a a' z) k m

theorem J_left (a : B) (m : M) : J b (a • m) = Lop b a * J b m :=
  LinearMap.ext fun z => J_left_apply_of b hone z (fun a a' => Lop_mul_apply b hone a a' z) a m

omit [SMulCommClass B Bᵐᵒᵖ M] hone in

theorem ell_mul_ell_of (g' : NF B X) (h : ∀ a : B, Lop b a * ell b g' = ell b (Lop b a g'))
    (g : NF B X) : ell b g * ell b g' = ell b (ell b g g') := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, LinearMap.add_apply, map_add]
  | single w k => rw [ell_single, mul_assoc, h, Pw_mul_ell, Module.End.mul_apply]

omit [SMulCommClass B Bᵐᵒᵖ M] hone in

theorem Lop_mul_Pw (w : List X) :
    ∀ a : B, Lop b a * Pw B w = ell b (Lop b a (Finsupp.single w 1)) := by
  induction w with
  | nil => intro a; simp [Lam_nil]
  | cons x v ih =>
    intro a
    have hx : (Finsupp.single (x :: v) 1 : NF B X) = Pw B [x] (Finsupp.single v 1) := by simp
    have ih' : ∀ a : B, Lop b a * ell b (Finsupp.single v 1) =
        ell b (Lop b a (Finsupp.single v 1)) := by
      intro a; rw [ell_single_one]; exact ih a
    rw [Pw_cons, ← mul_assoc, Lop_mul_Pw_some, hx, ← Module.End.mul_apply, Lop_mul_Pw_some,
      ← ell_single_one b v, J_apply, ell_mul_ell_of b _ ih']

theorem Lop_mul_ell (a : B) (g : NF B X) : Lop b a * ell b g = ell b (Lop b a g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, map_add, map_add]
  | single w k =>
    have hk : (Finsupp.single w k : NF B X) = k • Finsupp.single w 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hk, ell_smul b hone, LinearMap.map_smul, ell_smul b hone, ← mul_assoc, ell_single_one,
      Lop_mul_Pw b]

theorem ell_mul_ell (g g' : NF B X) : ell b g * ell b g' = ell b (ell b g g') :=
  ell_mul_ell_of b g' (fun a => Lop_mul_ell b hone a g') g

end Multiplicativity

end FRD.Pointed
