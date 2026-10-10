import FRD.Loc.Ops

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace FRD

open Matrix

variable {R : Type} [Ring R] [IsSylvesterDomain R]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

def distribEquivR (n m l : Type*) : ((n ⊕ m) ⊕ l) ⊕ l ≃ (n ⊕ l) ⊕ (m ⊕ l) where
  toFun := Sum.elim (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
    (Sum.inl ∘ Sum.inr)) (Sum.inr ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr))
    (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr)
  left_inv := by rintro (((i | i) | i) | i) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

def distribEquivL (n m l : Type*) : (l ⊕ (n ⊕ m)) ⊕ l ≃ (l ⊕ n) ⊕ (l ⊕ m) where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl)
    (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))) (Sum.inr ∘ Sum.inl)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr ∘ Sum.inl))
    (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr ∘ Sum.inr))
  left_inv := by rintro ((i | (i | i)) | i) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

section equivSimp
variable {n m l : Type*}

@[simp] theorem distribEquivR_1 (i : n) :
    distribEquivR n m l (Sum.inl (Sum.inl (Sum.inl i))) = Sum.inl (Sum.inl i) := rfl
@[simp] theorem distribEquivR_2 (i : m) :
    distribEquivR n m l (Sum.inl (Sum.inl (Sum.inr i))) = Sum.inr (Sum.inl i) := rfl
@[simp] theorem distribEquivR_3 (i : l) :
    distribEquivR n m l (Sum.inl (Sum.inr i)) = Sum.inl (Sum.inr i) := rfl
@[simp] theorem distribEquivR_4 (i : l) :
    distribEquivR n m l (Sum.inr i) = Sum.inr (Sum.inr i) := rfl

@[simp] theorem distribEquivL_1 (i : l) :
    distribEquivL n m l (Sum.inl (Sum.inl i)) = Sum.inl (Sum.inl i) := rfl
@[simp] theorem distribEquivL_2 (i : n) :
    distribEquivL n m l (Sum.inl (Sum.inr (Sum.inl i))) = Sum.inl (Sum.inr i) := rfl
@[simp] theorem distribEquivL_3 (i : m) :
    distribEquivL n m l (Sum.inl (Sum.inr (Sum.inr i))) = Sum.inr (Sum.inr i) := rfl
@[simp] theorem distribEquivL_4 (i : l) :
    distribEquivL n m l (Sum.inr i) = Sum.inr (Sum.inl i) := rfl

end equivSimp

namespace Display

theorem add_assoc_reindex (D : Display R n) (E : Display R m) (F : Display R l) :
    ((D.add E).add F).reindex (Equiv.sumAssoc n m l) = D.add (E.add F) := by
  apply Display.ext
  · ext (i | i | i) (j | j | j) <;> simp
  · ext (i | i | i) j <;> simp
  · ext i (j | j | j) <;> simp
  · simp [add_assoc]

theorem zero_add_reindex (D : Display R n) :
    ((scalar 0).add D).reindex (Equiv.emptySum Empty n) = D := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp
  · simp

theorem mul_assoc_reindex (D : Display R n) (E : Display R m) (F : Display R l) :
    ((D.mul E).mul F).reindex (Equiv.sumAssoc n m l) = D.mul (E.mul F) := by
  apply Display.ext
  · ext (i | i | i) (j | j | j) <;> simp [Matrix.mul_assoc]
  · ext (i | i | i) j <;> simp [Matrix.mul_assoc]
  · ext i (j | j | j) <;> simp [Matrix.mul_assoc]
  · simp [Matrix.mul_assoc]

theorem one_mul_reindex (D : Display R n) :
    ((scalar 1).mul D).reindex (Equiv.emptySum Empty n) = D := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp
  · simp

theorem mul_one_reindex (D : Display R n) :
    (D.mul (scalar 1)).reindex (Equiv.sumEmpty n Empty) = D := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp
  · simp

theorem eq_insL_scalar (D : Display R n) (h : D.x = 0) :
    D = ((scalar D.a).insL D.A D.full 0 D.u).reindex (Equiv.emptySum Empty n) := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp [h]
  · simp

theorem eq_insU_scalar (D : Display R n) (h : D.u = 0) :
    D = ((scalar D.a).insU D.A D.full 0 D.x).reindex (Equiv.emptySum Empty n) := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp [h]
  · ext i j; simp
  · simp

theorem scalar_add_scalar (a b : Matrix Unit Unit R) :
    ((scalar a).add (scalar b)).reindex (Equiv.sumEmpty Empty Empty) = scalar (a + b) := by
  apply Display.ext
  · ext i j; exact i.elim
  · ext i j; exact i.elim
  · ext i j; exact j.elim
  · simp

theorem scalar_mul_scalar (a b : Matrix Unit Unit R) :
    ((scalar a).mul (scalar b)).reindex (Equiv.sumEmpty Empty Empty) = scalar (a * b) := by
  apply Display.ext
  · ext i j; exact i.elim
  · ext i j; exact i.elim
  · ext i j; exact j.elim
  · simp

theorem right_distrib_key (D : Display R n) (E : Display R m) (F : Display R l)
    (hQ : IsFull (fromBlocks (1 : Matrix ((n ⊕ m) ⊕ l) ((n ⊕ m) ⊕ l) R) 0
      (fromCols 0 1) (1 : Matrix l l R)))
    (hP : IsFull (fromBlocks (1 : Matrix ((n ⊕ m) ⊕ l) ((n ⊕ m) ⊕ l) R) 0
      (fromCols 0 (-1)) (1 : Matrix l l R))) :
    ((((D.mul F).add (E.mul F)).reindex (distribEquivR n m l).symm).rmul _ hQ 0).lmul _ hP 0 =
      ((D.add E).mul F).insU F.A F.full (fromRows (fromRows 0 (E.u * F.x)) 0) (E.a * F.x) := by
  have hA : ((D.mul F).add (E.mul F)).A.submatrix (distribEquivR n m l) (distribEquivR n m l) =
      fromBlocks (fromBlocks (fromBlocks D.A 0 0 E.A) (fromRows (D.u * F.x) 0) 0 F.A)
        (fromRows (fromRows 0 (E.u * F.x)) 0) 0 F.A := by
    ext (((i | i) | i) | i) (((j | j) | j) | j) <;> simp
  have hu : ((D.mul F).add (E.mul F)).u.submatrix (distribEquivR n m l) id =
      fromRows (fromRows (fromRows (D.u * F.a) (E.u * F.a)) F.u) F.u := by
    ext (((i | i) | i) | i) j <;> simp
  have hx : ((D.mul F).add (E.mul F)).x.submatrix id (distribEquivR n m l) =
      fromCols (fromCols (fromCols D.x E.x) (D.a * F.x)) (E.a * F.x) := by
    ext i (((j | j) | j) | j) <;> simp
  apply Display.ext
  · simp only [lmul_A, rmul_A, reindex_A, Equiv.symm_symm, insU_A, hA]
    ext (((i | i) | i) | i) (((j | j) | j) | j) <;> blk_simp
  · simp only [lmul_u, rmul_u, rmul_A, reindex_u, reindex_A, Equiv.symm_symm, insU_u, hA, hu]
    ext (((i | i) | i) | i) j <;> blk_simp
  · simp only [lmul_x, lmul_A, rmul_x, rmul_A, reindex_x, reindex_A, Equiv.symm_symm, insU_x,
      hA, hx]
    ext i (((j | j) | j) | j) <;> blk_simp
  · simp only [lmul_a, lmul_u, rmul_a, rmul_u, rmul_x, rmul_A, reindex_a, reindex_u, reindex_x,
      reindex_A, Equiv.symm_symm, insU_a, hA, hx, hu]
    blk_simp

theorem left_distrib_key (D : Display R n) (E : Display R m) (F : Display R l)
    (hQ : IsFull (fromBlocks (1 : Matrix (l ⊕ (n ⊕ m)) (l ⊕ (n ⊕ m)) R)
      (fromRows (-1) 0) 0 (1 : Matrix l l R)))
    (hP : IsFull (fromBlocks (1 : Matrix (l ⊕ (n ⊕ m)) (l ⊕ (n ⊕ m)) R)
      (fromRows 1 0) 0 (1 : Matrix l l R))) :
    ((((F.mul D).add (F.mul E)).reindex (distribEquivL n m l).symm).rmul _ hQ 0).lmul _ hP 0 =
      (F.mul (D.add E)).insL F.A F.full (fromCols 0 (fromCols 0 (F.u * E.x))) (F.u * E.a) := by
  have hA : ((F.mul D).add (F.mul E)).A.submatrix (distribEquivL n m l) (distribEquivL n m l) =
      fromBlocks (fromBlocks F.A (fromCols (F.u * D.x) 0) 0 (fromBlocks D.A 0 0 E.A)) 0
        (fromCols 0 (fromCols 0 (F.u * E.x))) F.A := by
    ext ((i | (i | i)) | i) ((j | (j | j)) | j) <;> simp
  have hu : ((F.mul D).add (F.mul E)).u.submatrix (distribEquivL n m l) id =
      fromRows (fromRows (F.u * D.a) (fromRows D.u E.u)) (F.u * E.a) := by
    ext ((i | (i | i)) | i) j <;> simp
  have hx : ((F.mul D).add (F.mul E)).x.submatrix id (distribEquivL n m l) =
      fromCols (fromCols F.x (fromCols (F.a * D.x) (F.a * E.x))) F.x := by
    ext i ((j | (j | j)) | j) <;> simp
  apply Display.ext
  · simp only [lmul_A, rmul_A, reindex_A, Equiv.symm_symm, insL_A, hA]
    ext ((i | (i | i)) | i) ((j | (j | j)) | j) <;> blk_simp
  · simp only [lmul_u, rmul_u, rmul_A, reindex_u, reindex_A, Equiv.symm_symm, insL_u, hA, hu]
    ext ((i | (i | i)) | i) j <;> blk_simp
  · simp only [lmul_x, lmul_A, rmul_x, rmul_A, reindex_x, reindex_A, Equiv.symm_symm, insL_x,
      hA, hx]
    ext i ((j | (j | j)) | j) <;> blk_simp
  · simp only [lmul_a, lmul_u, rmul_a, rmul_u, rmul_x, rmul_A, reindex_a, reindex_u, reindex_x,
      reindex_A, Equiv.symm_symm, insL_a, hA, hx, hu]
    blk_simp

end Display

namespace Loc

open Display

theorem mk_of_x_eq_zero (D : Display R n) (h : D.x = 0) : mk D = mk (scalar D.a) := by
  conv_lhs => rw [D.eq_insL_scalar h]
  rw [mk_reindex, mk_insL]

theorem mk_of_u_eq_zero (D : Display R n) (h : D.u = 0) : mk D = mk (scalar D.a) := by
  conv_lhs => rw [D.eq_insU_scalar h]
  rw [mk_reindex, mk_insU]

protected theorem add_assoc (a b c : Loc R) : a + b + c = a + (b + c) := by
  induction a using Loc.ind with | h _ D => ?_
  induction b using Loc.ind with | h _ E => ?_
  induction c using Loc.ind with | h _ F => ?_
  rw [mk_add_mk, mk_add_mk, mk_add_mk, mk_add_mk, ← add_assoc_reindex, mk_reindex]

protected theorem zero_add (a : Loc R) : 0 + a = a := by
  induction a using Loc.ind with | h _ D => ?_
  rw [zero_def, mk_add_mk]
  conv_rhs => rw [← zero_add_reindex D]
  rw [mk_reindex]

protected theorem neg_add_cancel (a : Loc R) : -a + a = 0 := by
  induction a using Loc.ind with | h n D => ?_
  rw [neg_mk, mk_add_mk, zero_def]
  have hQ : IsFull (fromBlocks (1 : Matrix n n R) 0 (-1) (1 : Matrix n n R)) :=
    isFull_one.fromBlocks_lower isFull_one _
  have hP : IsFull (fromBlocks (1 : Matrix n n R) 0 1 (1 : Matrix n n R)) :=
    isFull_one.fromBlocks_lower isFull_one _
  have key : ((D.neg.add D).rmul _ hQ 0).lmul _ hP 0 =
      (⟨D.A, -D.u, 0, 0, D.full⟩ : Display R n).insU D.A D.full 0 D.x := by
    apply Display.ext <;> blk_simp
  calc mk (D.neg.add D) = mk (((D.neg.add D).rmul _ hQ 0).lmul _ hP 0) := by
        rw [mk_lmul, mk_rmul]
    _ = mk (scalar 0) := by rw [key, mk_insU, mk_of_x_eq_zero _ rfl]

protected theorem mul_assoc (a b c : Loc R) : a * b * c = a * (b * c) := by
  induction a using Loc.ind with | h _ D => ?_
  induction b using Loc.ind with | h _ E => ?_
  induction c using Loc.ind with | h _ F => ?_
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, ← mul_assoc_reindex, mk_reindex]

protected theorem one_mul (a : Loc R) : 1 * a = a := by
  induction a using Loc.ind with | h _ D => ?_
  rw [one_def, mk_mul_mk]
  conv_rhs => rw [← one_mul_reindex D]
  rw [mk_reindex]

protected theorem mul_one (a : Loc R) : a * 1 = a := by
  induction a using Loc.ind with | h _ D => ?_
  rw [one_def, mk_mul_mk]
  conv_rhs => rw [← mul_one_reindex D]
  rw [mk_reindex]

protected theorem right_distrib (a b c : Loc R) : (a + b) * c = a * c + b * c := by
  induction a using Loc.ind with | h n D => ?_
  induction b using Loc.ind with | h m E => ?_
  induction c using Loc.ind with | h l F => ?_
  rw [mk_add_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_add_mk]
  have hQ : IsFull (fromBlocks (1 : Matrix ((n ⊕ m) ⊕ l) ((n ⊕ m) ⊕ l) R) 0
      (fromCols 0 1) (1 : Matrix l l R)) := isFull_one.fromBlocks_lower isFull_one _
  have hP : IsFull (fromBlocks (1 : Matrix ((n ⊕ m) ⊕ l) ((n ⊕ m) ⊕ l) R) 0
      (fromCols 0 (-1)) (1 : Matrix l l R)) := isFull_one.fromBlocks_lower isFull_one _
  calc mk ((D.add E).mul F)
      = mk (((D.add E).mul F).insU F.A F.full (fromRows (fromRows 0 (E.u * F.x)) 0)
          (E.a * F.x)) := (mk_insU _ _ _ _ _).symm
    _ = mk ((D.mul F).add (E.mul F)) := by
        rw [← right_distrib_key D E F hQ hP, mk_lmul, mk_rmul, mk_reindex]

protected theorem left_distrib (c a b : Loc R) : c * (a + b) = c * a + c * b := by
  induction a using Loc.ind with | h n D => ?_
  induction b using Loc.ind with | h m E => ?_
  induction c using Loc.ind with | h l F => ?_
  rw [mk_add_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_add_mk]
  have hQ : IsFull (fromBlocks (1 : Matrix (l ⊕ (n ⊕ m)) (l ⊕ (n ⊕ m)) R)
      (fromRows (-1) 0) 0 (1 : Matrix l l R)) := isFull_one.fromBlocks_upper isFull_one _
  have hP : IsFull (fromBlocks (1 : Matrix (l ⊕ (n ⊕ m)) (l ⊕ (n ⊕ m)) R)
      (fromRows 1 0) 0 (1 : Matrix l l R)) := isFull_one.fromBlocks_upper isFull_one _
  calc mk (F.mul (D.add E))
      = mk ((F.mul (D.add E)).insL F.A F.full (fromCols 0 (fromCols 0 (F.u * E.x)))
          (F.u * E.a)) := (mk_insL _ _ _ _ _).symm
    _ = mk ((F.mul D).add (F.mul E)) := by
        rw [← left_distrib_key D E F hQ hP, mk_lmul, mk_rmul, mk_reindex]

noncomputable instance instRing : Ring (Loc R) :=
  Ring.ofMinimalAxioms Loc.add_assoc Loc.zero_add Loc.neg_add_cancel Loc.mul_assoc Loc.one_mul
    Loc.mul_one Loc.left_distrib Loc.right_distrib

theorem mk_scalar_add (a b : Matrix Unit Unit R) :
    mk (scalar a) + mk (scalar b) = mk (scalar (a + b)) := by
  rw [mk_add_mk, ← scalar_add_scalar, mk_reindex]

theorem mk_scalar_mul (a b : Matrix Unit Unit R) :
    mk (scalar a) * mk (scalar b) = mk (scalar (a * b)) := by
  rw [mk_mul_mk, ← scalar_mul_scalar, mk_reindex]

noncomputable def of : R →+* Loc R where
  toFun r := mk (scalar (Matrix.scalar Unit r))
  map_one' := by rw [map_one]; rfl
  map_mul' r s := by rw [map_mul]; exact (mk_scalar_mul _ _).symm
  map_zero' := by rw [map_zero]; rfl
  map_add' r s := by rw [map_add]; exact (mk_scalar_add _ _).symm

theorem of_apply (r : R) : of r = mk (scalar (Matrix.scalar Unit r)) := rfl

end Loc

end FRD
