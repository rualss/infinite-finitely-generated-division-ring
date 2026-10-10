import FRD.Core.RuleLemmas
import FRD.Core.Colimit

namespace FRD.Core

theorem map_ad_iterate {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R) (j : ℕ) (v : R) :
    f ((fun w => a * w - w * a)^[j] v) = (fun w => f a * w - w * f a)^[j] (f v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_sub, map_mul, map_mul]

theorem map_Kop {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) (j : ℕ) (v : R) :
    f (Kop a b j v) = Kop (f a) (f b) j (f v) := by
  unfold Kop
  rw [map_sub, map_mul, map_mul, map_ad_iterate]

section Tower

variable {F : Type} [DivisionRing F]

structure Stage (F : Type) [DivisionRing F] where

  B : Type
  [inst : DivisionRing B]

  i : F →+* B

  y : ℕ → B

attribute [instance] Stage.inst

structure StageExt (a₀ b₀ : F) (s : Stage F) (d : ℕ → s.B) where

  B' : Type
  [inst : DivisionRing B']

  φ : s.B →+* B'

  v : B'
  hv : ∀ j, Kop (φ (s.i a₀)) (φ (s.i b₀)) j v = φ (d j)

attribute [instance] StageExt.inst

def ExtProp (a₀ b₀ : F) : Prop :=
  ∀ (B : Type) (_ : DivisionRing B) (i : F →+* B) (d : ℕ → B),
    ∃ (B' : Type) (_ : DivisionRing B') (φ : B →+* B') (v : B'),
      ∀ j, Kop (φ (i a₀)) (φ (i b₀)) j v = φ (d j)

variable {a₀ b₀ : F}

noncomputable def stageExt (hext : ExtProp a₀ b₀) (n : ℕ) (s : Stage F) :
    StageExt a₀ b₀ s (fun j => rule (s.i a₀) (s.i b₀) s.y (n + 1) j) :=
  Classical.choice <| by
    obtain ⟨B', inst, φ, v, hv⟩ :=
      hext s.B s.inst s.i (fun j => rule (s.i a₀) (s.i b₀) s.y (n + 1) j)
    exact ⟨{ B' := B', φ := φ, v := v, hv := hv }⟩

noncomputable def next (hext : ExtProp a₀ b₀) (n : ℕ) (s : Stage F) : Stage F where
  B := (stageExt hext n s).B'
  i := (stageExt hext n s).φ.comp s.i
  y := fun m => if m = n + 1 then (stageExt hext n s).v else (stageExt hext n s).φ (s.y m)

noncomputable def nextHom (hext : ExtProp a₀ b₀) (n : ℕ) (s : Stage F) :
    s.B →+* (next hext n s).B :=
  (stageExt hext n s).φ

noncomputable def stage (hext : ExtProp a₀ b₀) : ℕ → Stage F
  | 0 => { B := F, i := RingHom.id F, y := fun _ => 0 }
  | n + 1 => next hext n (stage hext n)

noncomputable def stageHom (hext : ExtProp a₀ b₀) (n : ℕ) :
    (stage hext n).B →+* (stage hext (n + 1)).B :=
  nextHom hext n (stage hext n)

theorem stage_succ_i (hext : ExtProp a₀ b₀) (n : ℕ) (x : F) :
    (stage hext (n + 1)).i x = stageHom hext n ((stage hext n).i x) := rfl

theorem stage_succ_y_self (hext : ExtProp a₀ b₀) (n : ℕ) :
    (stage hext (n + 1)).y (n + 1) = (stageExt hext n (stage hext n)).v :=
  if_pos rfl

theorem stage_succ_y_of_ne (hext : ExtProp a₀ b₀) (n : ℕ) {m : ℕ} (hm : m ≠ n + 1) :
    (stage hext (n + 1)).y m = stageHom hext n ((stage hext n).y m) :=
  if_neg hm

theorem stage_succ_Kop (hext : ExtProp a₀ b₀) (n j : ℕ) :
    Kop ((stage hext (n + 1)).i a₀) ((stage hext (n + 1)).i b₀) j ((stage hext (n + 1)).y (n + 1)) =
      stageHom hext n
        (rule ((stage hext n).i a₀) ((stage hext n).i b₀) (stage hext n).y (n + 1) j) := by
  rw [stage_succ_y_self]
  exact (stageExt hext n (stage hext n)).hv j

end Tower

theorem exists_solution (h : FRD1) :
    ∃ (L : Type) (_ : DivisionRing L) (_ : CharP L 2) (a b : L) (y : ℕ → L),
      ∀ n, 1 ≤ n → ∀ j, Kop a b j (y n) = rule a b y n j := by
  obtain ⟨F, instF, charF, a₀, b₀, hext⟩ := h
  have hext' : ExtProp a₀ b₀ := hext
  obtain ⟨L, instL, ψ, hψ⟩ :=
    exists_chain_colimit (fun n => (stage hext' n).B) (fun n => stageHom hext' n)

  have hi : ∀ (n : ℕ) (x : F), ψ n ((stage hext' n).i x) = ψ 0 ((stage hext' 0).i x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => rw [stage_succ_i, hψ, ih]

  have hy : ∀ (n m : ℕ), m ≤ n →
      ψ n ((stage hext' n).y m) = ψ m ((stage hext' m).y m) := by
    intro n m hmn
    induction n with
    | zero =>
      obtain rfl : m = 0 := Nat.le_zero.1 hmn
      rfl
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · rfl
      · rw [stage_succ_y_of_ne hext' n (Nat.ne_of_lt hlt), hψ, ih (Nat.lt_succ_iff.1 hlt)]
  have hchar : CharP L 2 :=
    charP_of_injective_ringHom ((ψ 0).comp (stage hext' 0).i).injective 2
  refine ⟨L, instL, hchar, ψ 0 ((stage hext' 0).i a₀), ψ 0 ((stage hext' 0).i b₀),
    fun m => ψ m ((stage hext' m).y m), ?_⟩
  intro n hn j
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  calc Kop (ψ 0 ((stage hext' 0).i a₀)) (ψ 0 ((stage hext' 0).i b₀)) j
        (ψ (k + 1) ((stage hext' (k + 1)).y (k + 1)))
      = Kop (ψ (k + 1) ((stage hext' (k + 1)).i a₀)) (ψ (k + 1) ((stage hext' (k + 1)).i b₀)) j
          (ψ (k + 1) ((stage hext' (k + 1)).y (k + 1))) := by
        rw [hi (k + 1) a₀, hi (k + 1) b₀]
    _ = ψ k (rule ((stage hext' k).i a₀) ((stage hext' k).i b₀) (stage hext' k).y (k + 1) j) := by
        rw [← map_Kop, stage_succ_Kop, hψ]
    _ = rule (ψ 0 ((stage hext' 0).i a₀)) (ψ 0 ((stage hext' 0).i b₀))
          (fun i => ψ k ((stage hext' k).y i)) (k + 1) j := by
        rw [rule_map, hi k a₀, hi k b₀]
    _ = rule (ψ 0 ((stage hext' 0).i a₀)) (ψ 0 ((stage hext' 0).i b₀))
          (fun m => ψ m ((stage hext' m).y m)) (k + 1) j :=
        rule_congr (fun i _ hik => hy k i (Nat.lt_succ_iff.1 hik)) j

end FRD.Core
