# An infinite division ring finitely generated as a ring

Lean 4 + Mathlib proof of:

```lean
def FRD : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (_ : CharP D 2) (a b Y t s : D),
    Infinite D ∧ t * s = 1 ∧ Subring.closure {a, b, Y, t, s} = ⊤

def FRDStrong : Prop :=
  ∃ (D : Type) (_ : DivisionRing D) (_ : CharP D 2) (a b Y t s : D),
    Infinite D ∧ t * s = 1 ∧ Subring.closure {a, b, Y, t, s} = ⊤ ∧
    ∀ d : D, d ≠ 0 → ∃ N j : ℕ,
      d⁻¹ = s ^ N * (b * ((fun v => a * v - v * a)^[j] Y) - ((fun v => a * v - v * a)^[j] Y) * b)

theorem frd : FRD
theorem frdStrong : FRDStrong
```

There is an infinite division ring of characteristic 2 generated as a ring by five elements
(`Subring.closure`: closed under `+`, `-`, `*`, contains `0`, `1`; no inverses).

Statements: `FRD/Statement.lean` (the same in `Challenge.lean`; both import only Mathlib).
Proofs: `FRD/Main.lean`.

## Verification

```sh
lake exe cache get
lake build
FULL=1 ./scripts/audit.sh
./verification/comparator/run.sh
```

* `lake build` checks the proofs with the Lean kernel; `FinalCheck.lean` fails unless `frd` and
  `frdStrong` depend exactly on `propext`, `Classical.choice`, `Quot.sound`.
* `scripts/audit.sh` checks: no `sorry` and no axioms other than these three in any constant;
  no imports other than Mathlib; statements unchanged; kernel replay of every module
  (`leanchecker`). Expected last line: `ALL CHECKS PASSED`.
* `verification/comparator/run.sh` runs [Comparator](https://github.com/leanprover/comparator)
  with challenge `Challenge.lean` and solution `FRD.Main`: same statements, permitted axioms only,
  accepted by the Lean kernel and by [nanoda](https://github.com/ammkrn/nanoda_lib).
  Expected last line: `COMPARATOR CHECK PASSED`. Needs `go`, `cargo`, Linux with Landlock.
