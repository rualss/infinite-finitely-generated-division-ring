import FRD.Loc.Display

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace FRD

open Matrix

macro "blk_simp" : tactic =>
  `(tactic| simp [fromBlocks_multiply, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, fromRows_add_fromRows, fromCols_add_fromCols, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, add_comm, add_left_comm, add_assoc])

variable {R : Type} [Ring R] [IsSylvesterDomain R]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

namespace Display

def add (D : Display R n) (E : Display R m) : Display R (n ⊕ m) where
  A := fromBlocks D.A 0 0 E.A
  u := fromRows D.u E.u
  x := fromCols D.x E.x
  a := D.a + E.a
  full := D.full.fromBlocks_upper E.full 0

def mul (D : Display R n) (E : Display R m) : Display R (n ⊕ m) where
  A := fromBlocks D.A (D.u * E.x) 0 E.A
  u := fromRows (D.u * E.a) E.u
  x := fromCols D.x (D.a * E.x)
  a := D.a * E.a
  full := D.full.fromBlocks_upper E.full _

def neg (D : Display R n) : Display R n where
  A := D.A
  u := -D.u
  x := D.x
  a := -D.a
  full := D.full

@[simp] theorem add_A (D : Display R n) (E : Display R m) :
    (D.add E).A = fromBlocks D.A 0 0 E.A := rfl
@[simp] theorem add_u (D : Display R n) (E : Display R m) : (D.add E).u = fromRows D.u E.u := rfl
@[simp] theorem add_x (D : Display R n) (E : Display R m) : (D.add E).x = fromCols D.x E.x := rfl
@[simp] theorem add_a (D : Display R n) (E : Display R m) : (D.add E).a = D.a + E.a := rfl
@[simp] theorem mul_A (D : Display R n) (E : Display R m) :
    (D.mul E).A = fromBlocks D.A (D.u * E.x) 0 E.A := rfl
@[simp] theorem mul_u (D : Display R n) (E : Display R m) :
    (D.mul E).u = fromRows (D.u * E.a) E.u := rfl
@[simp] theorem mul_x (D : Display R n) (E : Display R m) :
    (D.mul E).x = fromCols D.x (D.a * E.x) := rfl
@[simp] theorem mul_a (D : Display R n) (E : Display R m) : (D.mul E).a = D.a * E.a := rfl
@[simp] theorem neg_A (D : Display R n) : D.neg.A = D.A := rfl
@[simp] theorem neg_u (D : Display R n) : D.neg.u = -D.u := rfl
@[simp] theorem neg_x (D : Display R n) : D.neg.x = D.x := rfl
@[simp] theorem neg_a (D : Display R n) : D.neg.a = -D.a := rfl

theorem reindex_add (D : Display R n) (e : n ≃ l) (E : Display R m) :
    (D.reindex e).add E = (D.add E).reindex (e.sumCongr (Equiv.refl m)) := by
  apply Display.ext
  · ext (i | i) (j | j) <;> simp
  · ext (i | i) j <;> simp
  · ext i (j | j) <;> simp
  · simp

theorem rmul_add (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R)
    (E : Display R m) :
    (D.rmul Q hQ f).add E =
      (D.add E).rmul (fromBlocks Q 0 0 1) (hQ.fromBlocks_upper isFull_one 0) (fromRows f 0) := by
  apply Display.ext <;> blk_simp

theorem lmul_add (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R)
    (E : Display R m) :
    (D.lmul P hP h).add E =
      (D.add E).lmul (fromBlocks P 0 0 1) (hP.fromBlocks_upper isFull_one 0) (fromCols h 0) := by
  apply Display.ext <;> blk_simp

theorem insU_add (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) (E : Display R m) :
    (D.insU G hG C p).add E =
      ((D.add E).insU G hG (fromRows C 0) p).reindex (sumRightComm n m g) := by
  apply Display.ext
  · ext ((i | i) | i) ((j | j) | j) <;> simp
  · ext ((i | i) | i) j <;> simp
  · ext i ((j | j) | j) <;> simp
  · simp

theorem insL_add (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) (E : Display R m) :
    (D.insL G hG C w).add E =
      ((D.add E).insL G hG (fromCols C 0) w).reindex (sumRightComm n m g) := by
  apply Display.ext
  · ext ((i | i) | i) ((j | j) | j) <;> simp
  · ext ((i | i) | i) j <;> simp
  · ext i ((j | j) | j) <;> simp
  · simp

theorem add_reindex_sumComm (D : Display R n) (E : Display R m) :
    (D.add E).reindex (Equiv.sumComm n m) = E.add D := by
  apply Display.ext
  · ext (i | i) (j | j) <;> simp
  · ext (i | i) j <;> simp
  · ext i (j | j) <;> simp
  · simp [add_comm]

theorem reindex_mul (D : Display R n) (e : n ≃ l) (E : Display R m) :
    (D.reindex e).mul E = (D.mul E).reindex (e.sumCongr (Equiv.refl m)) := by
  apply Display.ext
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply]
  · ext (i | i) j <;> simp [Matrix.mul_apply]
  · ext i (j | j) <;> simp
  · simp

theorem rmul_mul (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R)
    (E : Display R m) :
    (D.rmul Q hQ f).mul E =
      (D.mul E).rmul (fromBlocks Q (f * E.x) 0 1) (hQ.fromBlocks_upper isFull_one _)
        (fromRows (f * E.a) 0) := by
  apply Display.ext <;> blk_simp

theorem lmul_mul (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R)
    (E : Display R m) :
    (D.lmul P hP h).mul E =
      (D.mul E).lmul (fromBlocks P 0 0 1) (hP.fromBlocks_upper isFull_one 0) (fromCols h 0) := by
  apply Display.ext <;> blk_simp

theorem insU_mul (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) (E : Display R m) :
    (D.insU G hG C p).mul E =
      ((D.mul E).insU G hG (fromRows C 0) p).reindex (sumRightComm n m g) := by
  apply Display.ext
  · ext ((i | i) | i) ((j | j) | j) <;> simp
  · ext ((i | i) | i) j <;> simp
  · ext i ((j | j) | j) <;> simp
  · simp

theorem insL_mul (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) (E : Display R m) :
    (D.insL G hG C w).mul E =
      ((D.mul E).insL G hG (fromCols C (w * E.x)) (w * E.a)).reindex (sumRightComm n m g) := by
  apply Display.ext
  · ext ((i | i) | i) ((j | j) | j) <;> simp
  · ext ((i | i) | i) j <;> simp
  · ext i ((j | j) | j) <;> simp
  · simp

theorem mul_reindex (D : Display R n) (E : Display R m) (e : m ≃ l) :
    D.mul (E.reindex e) = (D.mul E).reindex ((Equiv.refl n).sumCongr e) := by
  apply Display.ext
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply]
  · ext (i | i) j <;> simp
  · ext i (j | j) <;> simp [Matrix.mul_apply]
  · simp

theorem mul_rmul (D : Display R n) (E : Display R m) (Q : Matrix m m R) (hQ : IsFull Q)
    (f : Matrix m Unit R) :
    D.mul (E.rmul Q hQ f) =
      (D.mul E).rmul (fromBlocks 1 0 0 Q) (isFull_one.fromBlocks_upper hQ 0) (fromRows 0 f) := by
  apply Display.ext <;> blk_simp

theorem mul_lmul (D : Display R n) (E : Display R m) (P : Matrix m m R) (hP : IsFull P)
    (h : Matrix Unit m R) :
    D.mul (E.lmul P hP h) =
      (D.mul E).lmul (fromBlocks 1 (D.u * h) 0 P) (isFull_one.fromBlocks_upper hP _)
        (fromCols 0 (D.a * h)) := by
  apply Display.ext <;> blk_simp

theorem mul_insU (D : Display R n) (E : Display R m) (G : Matrix g g R) (hG : IsFull G)
    (C : Matrix m g R) (p : Matrix Unit g R) :
    D.mul (E.insU G hG C p) =
      ((D.mul E).insU G hG (fromRows (D.u * p) C) (D.a * p)).reindex (Equiv.sumAssoc n m g) := by
  apply Display.ext
  · ext (i | i | i) (j | j | j) <;> simp
  · ext (i | i | i) j <;> simp
  · ext i (j | j | j) <;> simp
  · simp

theorem mul_insL (D : Display R n) (E : Display R m) (G : Matrix g g R) (hG : IsFull G)
    (C : Matrix g m R) (w : Matrix g Unit R) :
    D.mul (E.insL G hG C w) =
      ((D.mul E).insL G hG (fromCols 0 C) w).reindex (Equiv.sumAssoc n m g) := by
  apply Display.ext
  · ext (i | i | i) (j | j | j) <;> simp
  · ext (i | i | i) j <;> simp
  · ext i (j | j | j) <;> simp
  · simp

theorem reindex_neg (D : Display R n) (e : n ≃ l) : (D.reindex e).neg = D.neg.reindex e := by
  apply Display.ext <;> rfl

theorem rmul_neg (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).neg = D.neg.rmul Q hQ (-f) := by
  apply Display.ext <;> simp [add_comm]

theorem lmul_neg (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).neg = D.neg.lmul P hP h := by
  apply Display.ext <;> simp [add_comm]

theorem insU_neg (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : (D.insU G hG C p).neg = D.neg.insU G hG C p := by
  apply Display.ext <;> simp [fromRows_neg]

theorem insL_neg (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : (D.insL G hG C w).neg = D.neg.insL G hG C (-w) := by
  apply Display.ext <;> simp [fromRows_neg]

end Display

namespace Loc

open Display

theorem mk_add_comm (D : Display R n) (E : Display R m) : mk (D.add E) = mk (E.add D) := by
  rw [← add_reindex_sumComm, mk_reindex]

theorem mk_reindex_add (D : Display R n) (e : n ≃ l) (E : Display R m) :
    mk ((D.reindex e).add E) = mk (D.add E) := by
  rw [reindex_add, mk_reindex]

theorem mk_rmul_add (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R)
    (E : Display R m) : mk ((D.rmul Q hQ f).add E) = mk (D.add E) := by
  rw [rmul_add, mk_rmul]

theorem mk_lmul_add (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R)
    (E : Display R m) : mk ((D.lmul P hP h).add E) = mk (D.add E) := by
  rw [lmul_add, mk_lmul]

theorem mk_insU_add (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) (E : Display R m) : mk ((D.insU G hG C p).add E) = mk (D.add E) := by
  rw [insU_add, mk_reindex, mk_insU]

theorem mk_insL_add (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) (E : Display R m) : mk ((D.insL G hG C w).add E) = mk (D.add E) := by
  rw [insL_add, mk_reindex, mk_insL]

noncomputable instance : Add (Loc R) :=
  ⟨lift₂ (fun _ _ _ _ _ _ D E => mk (D.add E))
    (fun _ _ _ _ _ _ _ _ _ D e E => mk_reindex_add D e E)
    (fun _ _ _ _ _ _ D Q hQ f E => mk_rmul_add D Q hQ f E)
    (fun _ _ _ _ _ _ D P hP h E => mk_lmul_add D P hP h E)
    (fun _ _ _ _ _ _ _ _ _ D G hG C p E => mk_insU_add D G hG C p E)
    (fun _ _ _ _ _ _ _ _ _ D G hG C w E => mk_insL_add D G hG C w E)
    (fun _ _ _ _ _ _ _ _ _ D E e => by
      rw [mk_add_comm, mk_reindex_add, mk_add_comm])
    (fun _ _ _ _ _ _ D E Q hQ f => by
      rw [mk_add_comm, mk_rmul_add, mk_add_comm])
    (fun _ _ _ _ _ _ D E P hP h => by
      rw [mk_add_comm, mk_lmul_add, mk_add_comm])
    (fun _ _ _ _ _ _ _ _ _ D E G hG C p => by
      rw [mk_add_comm, mk_insU_add, mk_add_comm])
    (fun _ _ _ _ _ _ _ _ _ D E G hG C w => by
      rw [mk_add_comm, mk_insL_add, mk_add_comm])⟩

theorem mk_add_mk (D : Display R n) (E : Display R m) : mk D + mk E = mk (D.add E) :=
  lift₂_mk _ _ _ _ _ _ _ _ _ _ _ D E

noncomputable instance : Mul (Loc R) :=
  ⟨lift₂ (fun _ _ _ _ _ _ D E => mk (D.mul E))
    (fun _ _ _ _ _ _ _ _ _ D e E => by rw [reindex_mul, mk_reindex])
    (fun _ _ _ _ _ _ D Q hQ f E => by rw [rmul_mul, mk_rmul])
    (fun _ _ _ _ _ _ D P hP h E => by rw [lmul_mul, mk_lmul])
    (fun _ _ _ _ _ _ _ _ _ D G hG C p E => by rw [insU_mul, mk_reindex, mk_insU])
    (fun _ _ _ _ _ _ _ _ _ D G hG C w E => by rw [insL_mul, mk_reindex, mk_insL])
    (fun _ _ _ _ _ _ _ _ _ D E e => by rw [mul_reindex, mk_reindex])
    (fun _ _ _ _ _ _ D E Q hQ f => by rw [mul_rmul, mk_rmul])
    (fun _ _ _ _ _ _ D E P hP h => by rw [mul_lmul, mk_lmul])
    (fun _ _ _ _ _ _ _ _ _ D E G hG C p => by rw [mul_insU, mk_reindex, mk_insU])
    (fun _ _ _ _ _ _ _ _ _ D E G hG C w => by rw [mul_insL, mk_reindex, mk_insL])⟩

theorem mk_mul_mk (D : Display R n) (E : Display R m) : mk D * mk E = mk (D.mul E) :=
  lift₂_mk _ _ _ _ _ _ _ _ _ _ _ D E

noncomputable instance : Neg (Loc R) :=
  ⟨lift (fun _ _ _ D => mk D.neg)
    (fun _ _ _ _ _ _ D e => by rw [reindex_neg, mk_reindex])
    (fun _ _ _ D Q hQ f => by rw [rmul_neg, mk_rmul])
    (fun _ _ _ D P hP h => by rw [lmul_neg, mk_lmul])
    (fun _ _ _ _ _ _ D G hG C p => by rw [insU_neg, mk_insU])
    (fun _ _ _ _ _ _ D G hG C w => by rw [insL_neg, mk_insL])⟩

theorem neg_mk (D : Display R n) : -mk D = mk D.neg :=
  lift_mk _ _ _ _ _ _ D

noncomputable instance : Zero (Loc R) := ⟨mk (scalar 0)⟩
noncomputable instance : One (Loc R) := ⟨mk (scalar 1)⟩

theorem zero_def : (0 : Loc R) = mk (scalar 0) := rfl
theorem one_def : (1 : Loc R) = mk (scalar 1) := rfl

end Loc

end FRD
