import FRD.Core.Final.Code

open HahnSeries FRD.Laurent

namespace FRD.Core

section General
variable {R S : Type*} [Ring R] [Ring S]

theorem Expr.map_eval (f : R →+* S) (a b Y t s : R) (e : Expr) :
    f (e.eval a b Y t s) = e.eval (f a) (f b) (f Y) (f t) (f s) := by
  induction e with
  | a => rfl
  | b => rfl
  | Y => rfl
  | t => rfl
  | s => rfl
  | one => exact map_one f
  | add p q hp hq => simp only [Expr.eval, map_add, hp, hq]
  | mul p q hp hq => simp only [Expr.eval, map_mul, hp, hq]

theorem Expr.eval_mem_closure (a b Y t s : R) (e : Expr) :
    e.eval a b Y t s ∈ Subring.closure ({a, b, Y, t, s} : Set R) := by
  induction e with
  | a => exact Subring.subset_closure (by simp [Expr.eval])
  | b => exact Subring.subset_closure (by simp [Expr.eval])
  | Y => exact Subring.subset_closure (by simp [Expr.eval])
  | t => exact Subring.subset_closure (by simp [Expr.eval])
  | s => exact Subring.subset_closure (by simp [Expr.eval])
  | one => exact one_mem _
  | add p q hp hq => exact add_mem hp hq
  | mul p q hp hq => exact mul_mem hp hq

private theorem map_ad_iterate (f : R →+* S) (a v : R) (j : ℕ) :
    f ((fun w => a * w - w * a)^[j] v) = (fun w => f a * w - w * f a)^[j] (f v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [map_sub, map_mul, ih]

theorem ad_iterate_mem (T : Subring R) {a v : R} (ha : a ∈ T) (hv : v ∈ T) (j : ℕ) :
    (fun w => a * w - w * a)^[j] v ∈ T := by
  induction j with
  | zero => exact hv
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact sub_mem (mul_mem ha ih) (mul_mem ih ha)

theorem Kop_mem (T : Subring R) {a b v : R} (ha : a ∈ T) (hb : b ∈ T) (hv : v ∈ T) (j : ℕ) :
    Kop a b j v ∈ T := by
  unfold Kop
  exact sub_mem (mul_mem hb (ad_iterate_mem T ha hv j)) (mul_mem (ad_iterate_mem T ha hv j) hb)

end General

section Series
variable {L : Type*} [DivisionRing L]

theorem charP_two_series [CharP L 2] : CharP (HahnSeries ℤ L) 2 :=
  charP_of_injective_ringHom (f := (C : L →+* HahnSeries ℤ L)) C_injective 2

theorem single_one_pow_injective :
    Function.Injective (fun n : ℕ => (single (1 : ℤ) (1 : L)) ^ n) := by
  intro n m h
  simp only [single_pow, one_pow, nsmul_eq_mul, mul_one] at h
  have h' := congrArg HahnSeries.order h
  rw [order_single one_ne_zero, order_single one_ne_zero] at h'
  exact_mod_cast h'

noncomputable def S₀ (a b : L) (y : ℕ → L) : Subring (HahnSeries ℤ L) :=
  Subring.closure {C a, C b, Yser y, single 1 1, single (-1) 1}

theorem evalS_mem (a b : L) (y : ℕ → L) (e : Expr) : evalS a b (Yser y) e ∈ S₀ a b y :=
  Expr.eval_mem_closure _ _ _ _ _ e

theorem exists_evalS_of_mem [CharP L 2] (a b : L) (y : ℕ → L) {x : HahnSeries ℤ L}
    (hx : x ∈ S₀ a b y) : ∃ e, evalS a b (Yser y) e = x := by
  have : CharP (HahnSeries ℤ L) 2 := charP_two_series
  unfold S₀ at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [⟨.a, rfl⟩, ⟨.b, rfl⟩, ⟨.Y, rfl⟩, ⟨.t, rfl⟩, ⟨.s, rfl⟩]
  | zero => exact ⟨.add .one .one, CharTwo.add_self_eq_zero (1 : HahnSeries ℤ L)⟩
  | one => exact ⟨.one, rfl⟩
  | add u v _ _ hu hv =>
    obtain ⟨p, rfl⟩ := hu
    obtain ⟨q, rfl⟩ := hv
    exact ⟨.add p q, rfl⟩
  | neg u _ hu =>
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, (CharTwo.neg_eq _).symm⟩
  | mul u v _ _ hu hv =>
    obtain ⟨p, rfl⟩ := hu
    obtain ⟨q, rfl⟩ := hv
    exact ⟨.mul p q, rfl⟩

variable [CharP L 2] (a b : L) (y : ℕ → L)
  (hy : ∀ n, 1 ≤ n → ∀ j, Kop a b j (y n) = rule a b y n j)

include hy in

theorem inv_mem_S₀ {x : HahnSeries ℤ L} (hx : x ∈ S₀ a b y) : x⁻¹ ∈ S₀ a b y := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero]
    exact zero_mem _
  · obtain ⟨e, he⟩ := exists_evalS_of_mem a b y hx
    obtain ⟨j, rfl⟩ := enum_surjective e
    rw [inv_eq_code a b y hy j he.symm h0]
    exact mul_mem (pow_mem (evalS_mem a b y .s) _)
      (Kop_mem _ (evalS_mem a b y .a) (evalS_mem a b y .b) (evalS_mem a b y .Y) j)

noncomputable def Dfield : Subfield (HahnSeries ℤ L) :=
  { S₀ a b y with inv_mem' := fun _ hx => inv_mem_S₀ a b y hy hx }

theorem mem_Dfield {x : HahnSeries ℤ L} : x ∈ Dfield a b y hy ↔ x ∈ S₀ a b y := Iff.rfl

end Series

theorem frdStrong_of_subfield {L : Type} [DivisionRing L] [CharP L 2] (a b : L) (y : ℕ → L)
    (D : Subfield (HahnSeries ℤ L))
    (hmem : ∀ e, evalS a b (Yser y) e ∈ D)
    (hex : ∀ x ∈ D, ∃ e, evalS a b (Yser y) e = x)
    (hinv : ∀ j, evalS a b (Yser y) (enum j) ≠ 0 → ∃ N : ℕ,
      (evalS a b (Yser y) (enum j))⁻¹ = single (-1) (1 : L) ^ N * Kop (C a) (C b) j (Yser y)) :
    FRDStrong := by
  have : CharP (HahnSeries ℤ L) 2 := charP_two_series
  have hinj : Function.Injective D.subtype := D.subtype_injective
  have hchar : CharP D 2 := RingHom.charP D.subtype hinj 2
  obtain ⟨a', ha'⟩ : ∃ a' : D, D.subtype a' = C a := ⟨⟨_, hmem .a⟩, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : D, D.subtype b' = C b := ⟨⟨_, hmem .b⟩, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : D, D.subtype Y' = Yser y := ⟨⟨_, hmem .Y⟩, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : D, D.subtype t' = single 1 1 := ⟨⟨_, hmem .t⟩, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : D, D.subtype s' = single (-1) 1 := ⟨⟨_, hmem .s⟩, rfl⟩
  have heval : ∀ e : Expr, D.subtype (e.eval a' b' Y' t' s') = evalS a b (Yser y) e := by
    intro e
    rw [Expr.map_eval, ha', hb', hY', ht', hs']
    rfl
  refine ⟨D, inferInstance, hchar, a', b', Y', t', s', ?_, ?_, ?_, ?_⟩
  ·
    refine Infinite.of_injective (fun n : ℕ => t' ^ n) (fun n m h => ?_)
    have h' := congrArg D.subtype h
    simp only [map_pow, ht'] at h'
    exact single_one_pow_injective h'
  ·
    apply hinj
    rw [map_mul, ht', hs', single_mul_single, map_one D.subtype]
    simp
  ·
    rw [Subring.eq_top_iff']
    intro d
    obtain ⟨e, he⟩ := hex d.1 d.2
    have hd : d = e.eval a' b' Y' t' s' := hinj (by rw [heval e, he]; rfl)
    rw [hd]
    exact Expr.eval_mem_closure _ _ _ _ _ e
  ·
    intro d hd
    have hd' : (d : HahnSeries ℤ L) ≠ 0 := fun h => hd (hinj (by rw [map_zero]; exact h))
    obtain ⟨e, he⟩ := hex d.1 d.2
    obtain ⟨j, rfl⟩ := enum_surjective e
    obtain ⟨N, hN⟩ := hinv j (by rw [he]; exact hd')
    refine ⟨N, j, hinj ?_⟩
    rw [map_inv₀, map_mul, map_pow, map_sub, map_mul, map_mul, map_ad_iterate, ha', hb', hY', hs']
    rw [he] at hN
    exact hN

theorem frdStrong_of_solution {L : Type} [DivisionRing L] [CharP L 2] (a b : L) (y : ℕ → L)
    (hy : ∀ n, 1 ≤ n → ∀ j, Kop a b j (y n) = rule a b y n j) : FRDStrong :=
  frdStrong_of_subfield a b y (Dfield a b y hy) (fun e => evalS_mem a b y e)
    (fun _ hx => exists_evalS_of_mem a b y hx)
    (fun j hP => ⟨_, inv_eq_code a b y hy j rfl hP⟩)

end FRD.Core
