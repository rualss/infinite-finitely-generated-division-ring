import FRD.Core.Rule

open HahnSeries

namespace FRD.Core

variable {B : Type*} [DivisionRing B]

theorem Ytrunc_congr {y y' : ℕ → B} {n : ℕ} (h : ∀ i, 1 ≤ i → i < n → y i = y' i) :
    Ytrunc y n = Ytrunc y' n := by
  unfold Ytrunc
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [h i hi.1 hi.2]

theorem rule_congr {a b : B} {y y' : ℕ → B} {n : ℕ}
    (h : ∀ i, 1 ≤ i → i < n → y i = y' i) (j : ℕ) : rule a b y n j = rule a b y' n j := by
  unfold rule
  rw [Ytrunc_congr h]

section Map

variable {B' : Type*} [DivisionRing B']

theorem mapHom_injective (φ : B →+* B') : Function.Injective (Laurent.mapHom φ) := by
  intro P Q h
  ext n
  apply φ.injective
  rw [← Laurent.mapHom_coeff, ← Laurent.mapHom_coeff, h]

theorem mapHom_eq_zero_iff (φ : B →+* B') (P : HahnSeries ℤ B) :
    Laurent.mapHom φ P = 0 ↔ P = 0 := by
  constructor
  · intro h
    exact mapHom_injective φ (h.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

theorem mapHom_order (φ : B →+* B') (P : HahnSeries ℤ B) :
    (Laurent.mapHom φ P).order = P.order := by
  by_cases hP : P = 0
  · rw [hP, map_zero, order_zero, order_zero]
  · have hP' : Laurent.mapHom φ P ≠ 0 := fun h => hP ((mapHom_eq_zero_iff φ P).1 h)
    apply le_antisymm
    · apply order_le_of_coeff_ne_zero
      rw [Laurent.mapHom_coeff]
      intro h
      exact hP (coeff_order_eq_zero.1 (φ.injective (h.trans (map_zero φ).symm)))
    · apply order_le_of_coeff_ne_zero
      intro h
      apply hP'
      rw [← coeff_order_eq_zero, Laurent.mapHom_coeff, h, map_zero]

theorem mapHom_Ytrunc (φ : B →+* B') (y : ℕ → B) (n : ℕ) :
    Laurent.mapHom φ (Ytrunc y n) = Ytrunc (fun i => φ (y i)) n := by
  unfold Ytrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Laurent.mapHom_single]

theorem mapHom_evalS (φ : B →+* B') (a b : B) (Y : HahnSeries ℤ B) (e : Expr) :
    Laurent.mapHom φ (evalS a b Y e) = evalS (φ a) (φ b) (Laurent.mapHom φ Y) e := by
  unfold evalS
  induction e with
  | a => simp only [Expr.eval, Laurent.mapHom_C]
  | b => simp only [Expr.eval, Laurent.mapHom_C]
  | Y => simp only [Expr.eval]
  | t => simp only [Expr.eval, Laurent.mapHom_single, map_one]
  | s => simp only [Expr.eval, Laurent.mapHom_single, map_one]
  | one => simp only [Expr.eval, map_one]
  | add p q hp hq => simp only [Expr.eval, map_add, hp, hq]
  | mul p q hp hq => simp only [Expr.eval, map_mul, hp, hq]

end Map

theorem rule_map {B' : Type*} [DivisionRing B'] (φ : B →+* B') (a b : B) (y : ℕ → B) (n j : ℕ) :
    φ (rule a b y n j) = rule (φ a) (φ b) (fun i => φ (y i)) n j := by
  classical
  have hQ : evalS (φ a) (φ b) (Ytrunc (fun i => φ (y i)) n) (enum j) =
      Laurent.mapHom φ (evalS a b (Ytrunc y n) (enum j)) := by
    rw [mapHom_evalS, mapHom_Ytrunc]
  unfold rule
  simp only [hQ, mapHom_order, ne_eq, mapHom_eq_zero_iff]
  split_ifs with hc
  · rw [← map_inv₀, Laurent.mapHom_coeff]
  · exact map_zero φ

end FRD.Core
