import Mathlib

def FRD : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (_ : CharP D 2) (a b Y t s : D),
    Infinite D ∧ t * s = 0 ∧ Subring.closure {a, b, Y, t, s} = ⊤

theorem frd : FRD := sorry
