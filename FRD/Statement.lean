import Mathlib

def FRD : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (_ : CharP D 2) (a b Y t s : D),
    Infinite D ∧ t * s = 1 ∧ Subring.closure {a, b, Y, t, s} = ⊤

def FRDStrong : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (_ : CharP D 2) (a b Y t s : D),
    Infinite D ∧ t * s = 1 ∧ Subring.closure {a, b, Y, t, s} = ⊤ ∧
    ∀ d : D, d ≠ 0 → ∃ N j : ℕ,
      d⁻¹ = s ^ N * (b * ((fun v => a * v - v * a)^[j] Y) - ((fun v => a * v - v * a)^[j] Y) * b)
