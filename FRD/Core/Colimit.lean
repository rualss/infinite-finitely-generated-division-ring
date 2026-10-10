import FRD.Defs

namespace FRD

section Chain

variable (B : ℕ → Type) [∀ n, DivisionRing (B n)] (φ : ∀ n, B n →+* B (n + 1))

def chainMap (m n : ℕ) (h : m ≤ n) : B m →+* B n :=
  Nat.leRecOn (C := fun k => B m →+* B k) h (fun {k} g => (φ k).comp g) (RingHom.id (B m))

theorem chainMap_self (m : ℕ) : chainMap B φ m m le_rfl = RingHom.id (B m) :=
  Nat.leRecOn_self _

theorem chainMap_succ (m n : ℕ) (h : m ≤ n) :
    chainMap B φ m (n + 1) (Nat.le_succ_of_le h) = (φ n).comp (chainMap B φ m n h) :=
  Nat.leRecOn_succ h _

theorem chainMap_succ_self (n : ℕ) : chainMap B φ n (n + 1) (Nat.le_succ n) = φ n := by
  rw [chainMap_succ B φ n n le_rfl, chainMap_self, RingHom.comp_id]

theorem chainMap_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : B i) :
    chainMap B φ j k hjk (chainMap B φ i j hij x) = chainMap B φ i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [chainMap_self, RingHom.id_apply]
  | succ k hjk ih =>
    rw [chainMap_succ B φ j k hjk, chainMap_succ B φ i k (hij.trans hjk), RingHom.comp_apply,
      RingHom.comp_apply, ih]

instance chainMap_directedSystem : DirectedSystem B (fun i j h => chainMap B φ i j h) where
  map_self i x := by rw [chainMap_self, RingHom.id_apply]
  map_map _ _ _ hij hjk x := chainMap_trans B φ _ _ _ hij hjk x

end Chain

theorem exists_chain_colimit (B : ℕ → Type) [∀ n, DivisionRing (B n)]
    (φ : ∀ n, B n →+* B (n + 1)) :
    ∃ (L : Type) (_ : DivisionRing L) (ψ : ∀ n, B n →+* L),
      ∀ n x, ψ (n + 1) (φ n x) = ψ n x := by
  refine ⟨DirectLimit B (chainMap B φ), inferInstance,
    fun n => DirectLimit.Ring.of B (chainMap B φ) n, fun n x => ?_⟩
  have h := DirectLimit.Ring.of_f (G := B) (f := chainMap B φ) (Nat.le_succ n) x
  rwa [chainMap_succ_self] at h

end FRD
