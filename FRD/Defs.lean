import Mathlib
import FRD.Statement

open scoped TensorProduct

namespace FRD

def Kop {R : Type*} [Ring R] (a b : R) (j : ℕ) (v : R) : R :=
  b * ((fun w => a * w - w * a)^[j] v) - ((fun w => a * w - w * a)^[j] v) * b

def FRD1 : Prop :=
  ∃ (F : Type) (_ : DivisionRing F) (_ : CharP F 2) (a b : F),
    ∀ (B : Type) (_ : DivisionRing B) (i : F →+* B) (d : ℕ → B),
      ∃ (B' : Type) (_ : DivisionRing B') (φ : B →+* B') (v : B'),
        ∀ j, Kop (φ (i a)) (φ (i b)) j v = φ (d j)

section Matrix
variable {R : Type*} [Ring R]

def FactorsThrough {m n : Type*} (A : Matrix m n R) (r : ℕ) : Prop :=
  ∃ (P : Matrix m (Fin r) R) (Q : Matrix (Fin r) n R), A = P * Q

def IsFull {n : Type*} [Fintype n] (A : Matrix n n R) : Prop :=
  ∀ r : ℕ, FactorsThrough A r → Fintype.card n ≤ r

end Matrix

class IsSylvesterDomain (R : Type*) [Ring R] : Prop where
  nontrivial : Nontrivial R
  nullity : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R),
    A * B = 0 → ∃ r s : ℕ, r + s ≤ n ∧ FactorsThrough A r ∧ FactorsThrough B s

structure IsUniversalLoc {R K : Type} [Ring R] [Ring K] (ι : R →+* K) : Prop where
  injective : Function.Injective ι
  isUnit_map : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), IsFull A → IsUnit (A.map ι)
  exists_lift : ∀ (S : Type) [Ring S] (f : R →+* S),
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), IsFull A → IsUnit (A.map f)) →
    ∃ g : K →+* S, g.comp ι = f
  hom_ext : ∀ (S : Type) [Ring S] (g₁ g₂ : K →+* S), g₁.comp ι = g₂.comp ι → g₁ = g₂

structure DepReducing (R : Type*) [Ring R] (μ : R → ℕ) : Prop where
  size_eq_zero : ∀ x, μ x = 0 ↔ x = 0
  reduce : ∀ {ι : Type} (s : Finset ι) (a b : ι → R), ∑ i ∈ s, a i * b i = 0 →
    (∃ i ∈ s, a i ≠ 0) → (∀ i ∈ s, b i ≠ 0) →
    ∃ m ∈ s, ∃ c : ι → R, c m = 0 ∧ μ (b m - ∑ i ∈ s, c i * b i) < μ (b m)

structure WordBasis (B : Type*) [DivisionRing B] (X : Type*) (R : Type*) [Ring R] where
  ι : B →+* R
  word : List X → R
  coeff : R →+ (List X →₀ B)
  word_nil : word [] = 1
  word_append : ∀ u v, word (u ++ v) = word u * word v
  coeff_injective : Function.Injective coeff
  coeff_ι : ∀ c, coeff (ι c) = Finsupp.single [] c
  coeff_word_mul : ∀ (u : List X) (r : R) (w : List X), coeff (word u * r) (u ++ w) = coeff r w
  coeff_word_mul_of_not_prefix : ∀ (u : List X) (r : R) (w : List X),
    ¬ u <+: w → coeff (word u * r) w = 0
  coeff_mul_ι : ∀ (r : R) (c : B) (w : List X), coeff (r * ι c) w = coeff r w * c
  filtration : ∀ (c : B) (u w : List X), coeff (ι c * word u) w ≠ 0 → w.length ≤ u.length

section Env
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

abbrev Env (B : Type*) [Ring B] [Algebra (ZMod 2) B] : Type _ := B ⊗[ZMod 2] Bᵐᵒᵖ

def kappa (c : B) : Env B := c ⊗ₜ[ZMod 2] (1 : Bᵐᵒᵖ) - (1 : B) ⊗ₜ[ZMod 2] MulOpposite.op c

noncomputable def envMap {F : Type*} [Ring F] [Algebra (ZMod 2) F] (f : F →ₐ[ZMod 2] B) :
    Env F →ₐ[ZMod 2] Env B :=
  Algebra.TensorProduct.map f (AlgHom.op f)

end Env

section Bimodule
variable {B : Type*} [Ring B] {M : Type*} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]

def adBim (a : B) (m : M) : M := a • m - MulOpposite.op a • m

def KopBim (a b : B) (j : ℕ) (m : M) : M := adBim b ((adBim a)^[j] m)

end Bimodule

end FRD
