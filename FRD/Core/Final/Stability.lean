import FRD.Core.Rule

open HahnSeries FRD.Laurent

namespace FRD.Core

section Kop
variable {R : Type*} [Ring R]

theorem ad_iterate_zero (a : R) (j : ℕ) : (fun w => a * w - w * a)^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih]; simp

theorem Kop_zero (a b : R) (j : ℕ) : Kop a b j 0 = 0 := by
  simp [Kop, ad_iterate_zero]

end Kop

section Coeff
variable {B : Type*} [DivisionRing B]

theorem coeff_ad_iterate (a : B) (j : ℕ) (P : HahnSeries ℤ B) (n : ℤ) :
    ((fun w => C a * w - w * C a)^[j] P).coeff n = (fun w => a * w - w * a)^[j] (P.coeff n) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [coeff_sub, coeff_C_mul, coeff_mul_C, ih]

theorem coeff_Kop (a b : B) (j : ℕ) (P : HahnSeries ℤ B) (n : ℤ) :
    (Kop (C a) (C b) j P).coeff n = Kop a b j (P.coeff n) := by
  unfold Kop
  rw [coeff_sub, coeff_C_mul, coeff_mul_C, coeff_ad_iterate]

theorem coeff_Yser (y : ℕ → B) (m : ℤ) :
    (Yser y).coeff m = if 1 ≤ m then y m.toNat else 0 :=
  congrFun coeff_ofSuppBddBelow m

theorem coeff_Ytrunc (y : ℕ → B) (n : ℕ) (m : ℤ) :
    (Ytrunc y n).coeff m = if 1 ≤ m ∧ m < n then y m.toNat else 0 := by
  unfold Ytrunc
  rw [coeff_sum]
  simp only [coeff_single]
  split_ifs with h
  · rw [Finset.sum_eq_single m.toNat]
    · have hm : m = (m.toNat : ℤ) := by omega
      rw [if_pos hm]
    · intro i _ hi
      rw [if_neg]
      omega
    · intro hm
      exfalso
      apply hm
      rw [Finset.mem_Ico]
      omega
  · apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [if_neg]
    omega

theorem LB_Yser (y : ℕ → B) : LB 1 (Yser y) := by
  intro m hm
  rw [coeff_Yser, if_neg (not_le.2 hm)]

theorem LB_Ytrunc (y : ℕ → B) (n : ℕ) : LB 1 (Ytrunc y n) := by
  intro m hm
  rw [coeff_Ytrunc, if_neg]
  omega

theorem LB_Yser_sub_Ytrunc (y : ℕ → B) (n : ℕ) : LB n (Yser y - Ytrunc y n) := by
  intro m hm
  rw [coeff_sub, coeff_Yser, coeff_Ytrunc]
  by_cases h : 1 ≤ m
  · rw [if_pos h, if_pos ⟨h, hm⟩, sub_self]
  · rw [if_neg h, if_neg (fun h' => h h'.1), sub_self]

variable {a b : B} {Y : HahnSeries ℤ B}

theorem evalS_add (p q : Expr) : evalS a b Y (.add p q) = evalS a b Y p + evalS a b Y q := rfl

theorem evalS_mul (p q : Expr) : evalS a b Y (.mul p q) = evalS a b Y p * evalS a b Y q := rfl

theorem Expr.L_add (p q : Expr) : (Expr.add p q).L = max p.L q.L := rfl

theorem Expr.L_mul (p q : Expr) : (Expr.mul p q).L = p.L + q.L := rfl

theorem LB_evalS (hY : LB 1 Y) (e : Expr) : LB (-(e.L : ℤ)) (evalS a b Y e) := by
  induction e with
  | a => exact (LB_C a).mono (by simp [Expr.L])
  | b => exact (LB_C b).mono (by simp [Expr.L])
  | Y => exact hY.mono (by simp [Expr.L])
  | t => exact (LB_single 1 1).mono (by simp [Expr.L])
  | s => exact (LB_single (-1) 1).mono (by simp [Expr.L])
  | one => exact LB_one.mono (by simp [Expr.L])
  | add p q hp hq =>
    rw [evalS_add, Expr.L_add]
    exact (hp.mono (by push_cast; omega)).add (hq.mono (by push_cast; omega))
  | mul p q hp hq =>
    rw [evalS_mul, Expr.L_mul]
    exact (hp.mul hq).mono (by push_cast; omega)

theorem LB_evalS_sub {Y' Y'' : HahnSeries ℤ B} {n : ℤ} (h' : LB 1 Y') (h'' : LB 1 Y'')
    (h : LB n (Y' - Y'')) (e : Expr) :
    LB (n - (e.L : ℤ)) (evalS a b Y' e - evalS a b Y'' e) := by
  induction e with
  | a => show LB _ (C a - C a); rw [sub_self]; exact LB_zero _
  | b => show LB _ (C b - C b); rw [sub_self]; exact LB_zero _
  | Y => exact h.mono (by simp [Expr.L])
  | t => show LB _ (single 1 (1 : B) - single 1 1); rw [sub_self]; exact LB_zero _
  | s => show LB _ (single (-1) (1 : B) - single (-1) 1); rw [sub_self]; exact LB_zero _
  | one => show LB _ ((1 : HahnSeries ℤ B) - 1); rw [sub_self]; exact LB_zero _
  | add p q hp hq =>
    have e1 : evalS a b Y' (.add p q) - evalS a b Y'' (.add p q)
        = (evalS a b Y' p - evalS a b Y'' p) + (evalS a b Y' q - evalS a b Y'' q) := by
      simp only [evalS_add]; abel
    rw [e1, Expr.L_add]
    exact (hp.mono (by push_cast; omega)).add (hq.mono (by push_cast; omega))
  | mul p q hp hq =>
    have e1 : evalS a b Y' (.mul p q) - evalS a b Y'' (.mul p q)
        = (evalS a b Y' p - evalS a b Y'' p) * evalS a b Y' q
          + evalS a b Y'' p * (evalS a b Y' q - evalS a b Y'' q) := by
      simp only [evalS_mul]; noncomm_ring
    rw [e1, Expr.L_mul]
    exact ((hp.mul (LB_evalS h' q)).mono (by push_cast; omega)).add
      (((LB_evalS h'' p).mul hq).mono (by push_cast; omega))

theorem order_eq_of_LB {P : HahnSeries ℤ B} {k : ℤ} (hP : LB k P) (hk : P.coeff k ≠ 0) :
    P.order = k := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hk rfl
  apply le_antisymm (order_le_of_coeff_ne_zero hk)
  by_contra hlt
  exact hP0 (coeff_order_eq_zero.1 (hP _ (not_le.1 hlt)))

end Coeff

end FRD.Core
