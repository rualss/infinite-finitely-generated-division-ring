import FRD.Core.Final.Stability

open HahnSeries FRD.Laurent

namespace FRD.Core

variable {L : Type*} [DivisionRing L]

theorem le_codeN (k : ℤ) (l : ℕ) : 2 * k + l + 1 ≤ (codeN k l : ℤ) := Int.self_le_toNat _

theorem rule_eq_of_visible {a b : L} {y : ℕ → L} {n j : ℕ} {Q : HahnSeries ℤ L}
    (hQ : Q = evalS a b (Ytrunc y n) (enum j)) (h0 : Q ≠ 0)
    (hvis : Q.order < (n : ℤ) - ((enum j).L : ℤ)) :
    rule a b y n j = (Q⁻¹).coeff ((n : ℤ) - (codeN Q.order (enum j).L : ℤ)) := by
  subst hQ
  unfold rule
  exact if_pos ⟨h0, hvis⟩

theorem rule_eq_zero {a b : L} {y : ℕ → L} {n j : ℕ} {Q : HahnSeries ℤ L}
    (hQ : Q = evalS a b (Ytrunc y n) (enum j))
    (h : ¬ (Q ≠ 0 ∧ Q.order < (n : ℤ) - ((enum j).L : ℤ))) :
    rule a b y n j = 0 := by
  subst hQ
  unfold rule
  exact if_neg h

theorem code_identity (a b : L) (y : ℕ → L)
    (hy : ∀ n, 1 ≤ n → ∀ j, Kop a b j (y n) = rule a b y n j) (j : ℕ) {P : HahnSeries ℤ L}
    (hPdef : P = evalS a b (Yser y) (enum j)) (hP : P ≠ 0) :
    Kop (C a) (C b) j (Yser y) = single ((codeN P.order (enum j).L : ℕ) : ℤ) 1 * P⁻¹ := by
  obtain ⟨k, hk⟩ : ∃ k, k = P.order := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = (enum j).L := ⟨_, rfl⟩
  rw [← hk, ← hl]
  have hLBk : LB k P := hk ▸ LB_order P
  have hPk : P.coeff k ≠ 0 := fun h => hP (coeff_order_eq_zero.1 (hk ▸ h))
  have hinv : LB (-k) P⁻¹ := LB_inv hLBk hPk
  have hN := le_codeN k l
  obtain ⟨N, hNdef⟩ : ∃ N, N = codeN k l := ⟨_, rfl⟩
  rw [← hNdef] at hN ⊢
  ext n
  rw [coeff_Kop, coeff_single_one_mul, coeff_Yser]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn]
    obtain ⟨m, hm⟩ : ∃ m, m = n.toNat := ⟨_, rfl⟩
    have hm1 : 1 ≤ m := by omega
    have hmn : (m : ℤ) = n := by omega
    rw [← hm, hy m hm1 j]
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = evalS a b (Ytrunc y m) (enum j) := ⟨_, rfl⟩
    have hPQ : LB ((m : ℤ) - l) (P - Q) := by
      rw [hPdef, hQdef, hl]
      exact LB_evalS_sub (LB_Yser y) (LB_Ytrunc y m) (LB_Yser_sub_Ytrunc y m) (enum j)
    have hcoeff : ∀ i : ℤ, i < (m : ℤ) - l → Q.coeff i = P.coeff i := by
      intro i hi
      have h := hPQ i hi
      rw [coeff_sub, sub_eq_zero] at h
      exact h.symm
    by_cases hvis : k < (m : ℤ) - l
    ·
      have hQk : Q.coeff k ≠ 0 := by
        rw [hcoeff k hvis]
        exact hPk
      have hLBQ : LB k Q := by
        intro i hi
        rw [hcoeff i (by omega)]
        exact hLBk i hi
      have hQord : Q.order = k := order_eq_of_LB hLBQ hQk
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        exact hQk rfl
      have hrule : rule a b y m j = (Q⁻¹).coeff ((m : ℤ) - (N : ℤ)) := by
        rw [rule_eq_of_visible hQdef hQ0 (by rw [hQord, ← hl]; exact hvis), hQord, ← hl, ← hNdef]
      rw [hrule, hmn]
      have h := LB_inv_sub_inv hLBk hPk hLBQ hQk hPQ (n - N) (by omega)
      rw [coeff_sub, sub_eq_zero] at h
      exact h.symm
    ·
      have hrule : rule a b y m j = 0 := by
        apply rule_eq_zero hQdef
        rintro ⟨hQ0, hQlt⟩
        apply hQ0
        apply coeff_order_eq_zero.1
        rw [← hl] at hQlt
        rw [hcoeff _ hQlt]
        exact hLBk _ (by omega)
      rw [hrule]
      exact (hinv _ (by omega)).symm
  · rw [if_neg hn, Kop_zero]
    exact (hinv _ (by omega)).symm

theorem inv_eq_code (a b : L) (y : ℕ → L)
    (hy : ∀ n, 1 ≤ n → ∀ j, Kop a b j (y n) = rule a b y n j) (j : ℕ) {P : HahnSeries ℤ L}
    (hPdef : P = evalS a b (Yser y) (enum j)) (hP : P ≠ 0) :
    P⁻¹ = single (-1) (1 : L) ^ codeN P.order (enum j).L * Kop (C a) (C b) j (Yser y) := by
  rw [code_identity a b y hy j hPdef hP, ← mul_assoc, single_pow, single_mul_single]
  have h : codeN P.order (enum j).L • (-1 : ℤ) + (codeN P.order (enum j).L : ℤ) = 0 := by simp
  rw [h, one_pow, mul_one, single_zero_one, one_mul]

end FRD.Core
