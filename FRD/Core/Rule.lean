import FRD.Series.Laurent

open HahnSeries

namespace FRD.Core

inductive Expr : Type
  | a | b | Y | t | s
  | one
  | add (p q : Expr)
  | mul (p q : Expr)
  deriving Countable

instance : Nonempty Expr := ⟨Expr.one⟩

def Expr.eval {R : Type*} [Ring R] (a b Y t s : R) : Expr → R
  | .a => a
  | .b => b
  | .Y => Y
  | .t => t
  | .s => s
  | .one => 1
  | .add p q => p.eval a b Y t s + q.eval a b Y t s
  | .mul p q => p.eval a b Y t s * q.eval a b Y t s

def Expr.L : Expr → ℕ
  | .s => 1
  | .add p q => max p.L q.L
  | .mul p q => p.L + q.L
  | _ => 0

noncomputable def enum : ℕ → Expr := Classical.choose (exists_surjective_nat Expr)

theorem enum_surjective : Function.Surjective enum := Classical.choose_spec (exists_surjective_nat Expr)

def codeN (k : ℤ) (L : ℕ) : ℕ := Int.toNat (2 * k + L + 1)

section Series
variable {B : Type*} [DivisionRing B]

noncomputable def Ytrunc (y : ℕ → B) (n : ℕ) : HahnSeries ℤ B :=
  ∑ i ∈ Finset.Ico 1 n, single (i : ℤ) (y i)

noncomputable def Yser (y : ℕ → B) : HahnSeries ℤ B :=
  HahnSeries.ofSuppBddBelow (fun m : ℤ => if 1 ≤ m then y m.toNat else 0)
    ⟨1, fun m hm => by
      by_contra h
      exact hm (if_neg h)⟩

noncomputable def evalS (a b : B) (Y : HahnSeries ℤ B) (e : Expr) : HahnSeries ℤ B :=
  e.eval (C a) (C b) Y (single 1 1) (single (-1) 1)

noncomputable def rule (a b : B) (y : ℕ → B) (n j : ℕ) : B :=
  open Classical in
  let Q := evalS a b (Ytrunc y n) (enum j)
  if Q ≠ 0 ∧ Q.order < (n : ℤ) - ((enum j).L : ℤ) then
    (Q⁻¹).coeff ((n : ℤ) - (codeN Q.order (enum j).L : ℤ))
  else 0

end Series

end FRD.Core
