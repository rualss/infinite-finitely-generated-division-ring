import FRD.Loc.Ring

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace FRD

open Matrix

variable {R : Type} [Ring R] [IsSylvesterDomain R]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

namespace Display

omit [IsSylvesterDomain R] in
theorem whole_scalar (a : Matrix Unit Unit R) :
    (scalar a).whole.submatrix (Equiv.emptySum Empty Unit).symm (Equiv.emptySum Empty Unit).symm
      = a := by
  ext i j; simp [whole, scalar]

omit [IsSylvesterDomain R] in
theorem isFull_whole_scalar (a : Matrix Unit Unit R) : IsFull (scalar a).whole ↔ a ≠ 0 := by
  rw [← isFull_submatrix_equiv (Equiv.emptySum Empty Unit).symm, whole_scalar,
    isFull_iff_ne_zero_of_unique]

def inv (D : Display R n) (hW : IsFull D.whole) : Display R (n ⊕ Unit) where
  A := D.whole
  u := fromRows 0 1
  x := fromCols 0 (-1)
  a := 0
  full := hW

theorem eq_lmul_rmul_of_factors (D : Display R n) (P₀ : Matrix n n R) (p₀ : Matrix Unit n R)
    (Q₀ : Matrix n n R) (q₀ : Matrix n Unit R) (hP : IsFull P₀) (hQ : IsFull Q₀)
    (h : D.whole = fromRows P₀ p₀ * fromCols Q₀ q₀) :
    D = ((⟨1, 0, 0, 0, isFull_one⟩ : Display R n).rmul Q₀ hQ q₀).lmul P₀ hP p₀ := by
  rw [whole, fromRows_mul_fromCols, fromBlocks_inj] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply Display.ext <;> simp [h1, h2, h3, h4]

theorem mul_inv_key (D : Display R n) (hW : IsFull D.whole)
    (hQ : IsFull (fromBlocks (1 : Matrix n n R) (fromCols (-1) 0) 0
      (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R)))
    (hP : IsFull (fromBlocks (1 : Matrix n n R) (fromCols 1 0) 0
      (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R))) :
    (((D.mul (D.inv hW)).lmul 1 isFull_one (fromCols 0 (fromCols 0 1))).rmul _ hQ 0).lmul _ hP 0 =
      (⟨D.A, 0, D.x, 1, D.full⟩ : Display R n).insL D.whole hW 0 (fromRows 0 1) := by
  apply Display.ext <;> simp only [inv, whole, lmul_A, lmul_u, lmul_x, lmul_a, rmul_A, rmul_u,
    rmul_x, rmul_a, mul_A, mul_u, mul_x, mul_a, insL_A, insL_u, insL_x, insL_a] <;> blk_simp

theorem inv_mul_key (D : Display R n) (hW : IsFull D.whole)
    (hP : IsFull (fromBlocks (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R) (fromRows 1 0) 0
      (1 : Matrix n n R)))
    (hQ : IsFull (fromBlocks (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R) (fromRows (-1) 0) 0
      (1 : Matrix n n R))) :
    ((((D.inv hW).mul D).rmul 1 isFull_one (fromRows (fromRows 0 (-1)) 0)).lmul _ hP 0).rmul _ hQ 0
      = (⟨D.whole, 0, fromCols 0 (-1), 1, hW⟩ : Display R (n ⊕ Unit)).insL D.A D.full 0 D.u := by
  apply Display.ext <;> simp only [inv, whole, lmul_A, lmul_u, lmul_x, lmul_a, rmul_A, rmul_u,
    rmul_x, rmul_a, mul_A, mul_u, mul_x, mul_a, insL_A, insL_u, insL_x, insL_a] <;> blk_simp

end Display

namespace Loc

open Display

theorem wholeFull_scalar (a : Matrix Unit Unit R) : WholeFull (mk (scalar a)) ↔ a ≠ 0 := by
  rw [wholeFull_mk, isFull_whole_scalar]

theorem scalar_eq_zero_of_mk_eq {a : Matrix Unit Unit R} (h : mk (scalar a) = (0 : Loc R)) :
    a = 0 := by
  by_contra ha
  have h1 := (wholeFull_scalar a).2 ha
  rw [h, zero_def, wholeFull_scalar] at h1
  exact h1 rfl

theorem of_injective : Function.Injective (of : R →+* Loc R) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have h := scalar_eq_zero_of_mk_eq (a := Matrix.scalar Unit r) hr
  rw [← map_zero (Matrix.scalar Unit)] at h
  exact Matrix.scalar_inj.1 h

instance : Nontrivial (Loc R) := by
  have := IsSylvesterDomain.nontrivial (R := R)
  exact of_injective.nontrivial

theorem eq_zero_of_not_wholeFull (D : Display R n) (h : ¬ IsFull D.whole) : mk D = 0 := by
  classical
  rw [IsFull] at h
  push Not at h
  obtain ⟨r, hr, hlt⟩ := h
  have hr' : FactorsThrough D.whole (Fintype.card n) := by
    refine hr.mono ?_
    simp only [Fintype.card_sum, Fintype.card_unique] at hlt
    omega
  obtain ⟨P, Q, hPQ⟩ := hr'
  let e := Fintype.equivFin n
  have h1 : D.whole = P.submatrix id e * Q.submatrix e id := by
    rw [Matrix.submatrix_mul_equiv, hPQ]; simp
  rw [← fromRows_toRows (P.submatrix id e), ← fromCols_toCols (Q.submatrix e id)] at h1
  have hA : D.A = (P.submatrix id e).toRows₁ * (Q.submatrix e id).toCols₁ := by
    have h2 := h1
    rw [whole, fromRows_mul_fromCols, fromBlocks_inj] at h2
    exact h2.1
  have hP : IsFull (P.submatrix id e).toRows₁ := IsFull.of_mul_right (hA ▸ D.full)
  have hQ : IsFull (Q.submatrix e id).toCols₁ := IsFull.of_mul_left (hA ▸ D.full)
  rw [D.eq_lmul_rmul_of_factors _ _ _ _ hP hQ h1, mk_lmul, mk_rmul, mk_of_x_eq_zero _ rfl]
  rfl

theorem mk_mul_inv (D : Display R n) (hW : IsFull D.whole) : mk D * mk (D.inv hW) = 1 := by
  have hQ : IsFull (fromBlocks (1 : Matrix n n R) (fromCols (-1) 0) 0
      (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R)) := isFull_one.fromBlocks_upper isFull_one _
  have hP : IsFull (fromBlocks (1 : Matrix n n R) (fromCols 1 0) 0
      (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R)) := isFull_one.fromBlocks_upper isFull_one _
  rw [mk_mul_mk]
  calc mk (D.mul (D.inv hW))
      = mk ((((D.mul (D.inv hW)).lmul 1 isFull_one (fromCols 0 (fromCols 0 1))).rmul _ hQ 0).lmul
          _ hP 0) := by rw [mk_lmul, mk_rmul, mk_lmul]
    _ = 1 := by rw [mul_inv_key D hW hQ hP, mk_insL, mk_of_u_eq_zero _ rfl]; rfl

theorem mk_inv_mul (D : Display R n) (hW : IsFull D.whole) : mk (D.inv hW) * mk D = 1 := by
  have hP : IsFull (fromBlocks (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R) (fromRows 1 0) 0
      (1 : Matrix n n R)) := isFull_one.fromBlocks_upper isFull_one _
  have hQ : IsFull (fromBlocks (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) R) (fromRows (-1) 0) 0
      (1 : Matrix n n R)) := isFull_one.fromBlocks_upper isFull_one _
  rw [mk_mul_mk]
  calc mk ((D.inv hW).mul D)
      = mk (((((D.inv hW).mul D).rmul 1 isFull_one (fromRows (fromRows 0 (-1)) 0)).lmul _ hP
          0).rmul _ hQ 0) := by rw [mk_rmul, mk_lmul, mk_rmul]
    _ = 1 := by rw [inv_mul_key D hW hP hQ, mk_insL, mk_of_u_eq_zero _ rfl]; rfl

theorem isUnit_or_eq_zero (z : Loc R) : IsUnit z ∨ z = 0 := by
  induction z using Loc.ind with | h n D => ?_
  by_cases hW : IsFull D.whole
  · exact Or.inl (isUnit_iff_exists.2 ⟨mk (D.inv hW), mk_mul_inv D hW, mk_inv_mul D hW⟩)
  · exact Or.inr (eq_zero_of_not_wholeFull D hW)

noncomputable instance instDivisionRing : DivisionRing (Loc R) :=
  DivisionRing.ofIsUnitOrEqZero isUnit_or_eq_zero

end Loc

end FRD
