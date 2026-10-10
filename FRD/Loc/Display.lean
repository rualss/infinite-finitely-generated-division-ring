import FRD.Loc.Full

namespace FRD

open Matrix

def sumRightComm (α β γ : Type*) : (α ⊕ β) ⊕ γ ≃ (α ⊕ γ) ⊕ β where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  left_inv := by rintro ((a | b) | c) <;> rfl
  right_inv := by rintro ((a | c) | b) <;> rfl

section sumRightComm
variable {α β γ : Type*}

@[simp] theorem sumRightComm_inl_inl (a : α) :
    sumRightComm α β γ (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inl a) := rfl
@[simp] theorem sumRightComm_inl_inr (b : β) :
    sumRightComm α β γ (Sum.inl (Sum.inr b)) = Sum.inr b := rfl
@[simp] theorem sumRightComm_inr (c : γ) :
    sumRightComm α β γ (Sum.inr c) = Sum.inl (Sum.inr c) := rfl
@[simp] theorem sumRightComm_symm : (sumRightComm α β γ).symm = sumRightComm α γ β := rfl

end sumRightComm

@[ext]
structure Display (R : Type) [Ring R] (n : Type) [Fintype n] [DecidableEq n] where

  A : Matrix n n R

  u : Matrix n Unit R

  x : Matrix Unit n R

  a : Matrix Unit Unit R
  full : IsFull A

variable {R : Type} [Ring R]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

namespace Display

def whole (D : Display R n) : Matrix (n ⊕ Unit) (n ⊕ Unit) R := fromBlocks D.A D.u D.x D.a

def reindex (D : Display R n) (e : n ≃ m) : Display R m where
  A := D.A.submatrix e.symm e.symm
  u := D.u.submatrix e.symm id
  x := D.x.submatrix id e.symm
  a := D.a
  full := D.full.reindex e

@[simp] theorem reindex_A (D : Display R n) (e : n ≃ m) :
    (D.reindex e).A = D.A.submatrix e.symm e.symm := rfl
@[simp] theorem reindex_u (D : Display R n) (e : n ≃ m) :
    (D.reindex e).u = D.u.submatrix e.symm id := rfl
@[simp] theorem reindex_x (D : Display R n) (e : n ≃ m) :
    (D.reindex e).x = D.x.submatrix id e.symm := rfl
@[simp] theorem reindex_a (D : Display R n) (e : n ≃ m) : (D.reindex e).a = D.a := rfl

@[simp] theorem reindex_refl (D : Display R n) : D.reindex (Equiv.refl n) = D := by
  apply Display.ext <;> simp

@[simp] theorem reindex_reindex (D : Display R n) (e : n ≃ m) (e' : m ≃ l) :
    (D.reindex e).reindex e' = D.reindex (e.trans e') := by
  apply Display.ext <;> simp [Function.comp_def]

def scalar (a : Matrix Unit Unit R) : Display R Empty where
  A := 0
  u := 0
  x := 0
  a := a
  full := isFull_of_isEmpty _

@[simp] theorem scalar_a (a : Matrix Unit Unit R) : (scalar a).a = a := rfl

variable [IsSylvesterDomain R]

def rmul (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    Display R n where
  A := D.A * Q
  u := D.u + D.A * f
  x := D.x * Q
  a := D.a + D.x * f
  full := D.full.mul hQ

def lmul (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    Display R n where
  A := P * D.A
  u := P * D.u
  x := D.x + h * D.A
  a := D.a + h * D.u
  full := hP.mul D.full

def insU (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : Display R (n ⊕ g) where
  A := fromBlocks D.A C 0 G
  u := fromRows D.u 0
  x := fromCols D.x p
  a := D.a
  full := D.full.fromBlocks_upper hG C

def insL (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : Display R (n ⊕ g) where
  A := fromBlocks D.A 0 C G
  u := fromRows D.u w
  x := fromCols D.x 0
  a := D.a
  full := D.full.fromBlocks_lower hG C

section simps
variable (D : Display R n)

@[simp] theorem rmul_A (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).A = D.A * Q := rfl
@[simp] theorem rmul_u (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).u = D.u + D.A * f := rfl
@[simp] theorem rmul_x (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).x = D.x * Q := rfl
@[simp] theorem rmul_a (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).a = D.a + D.x * f := rfl

@[simp] theorem lmul_A (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).A = P * D.A := rfl
@[simp] theorem lmul_u (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).u = P * D.u := rfl
@[simp] theorem lmul_x (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).x = D.x + h * D.A := rfl
@[simp] theorem lmul_a (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).a = D.a + h * D.u := rfl

@[simp] theorem insU_A (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : (D.insU G hG C p).A = fromBlocks D.A C 0 G := rfl
@[simp] theorem insU_u (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : (D.insU G hG C p).u = fromRows D.u 0 := rfl
@[simp] theorem insU_x (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : (D.insU G hG C p).x = fromCols D.x p := rfl
@[simp] theorem insU_a (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : (D.insU G hG C p).a = D.a := rfl

@[simp] theorem insL_A (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : (D.insL G hG C w).A = fromBlocks D.A 0 C G := rfl
@[simp] theorem insL_u (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : (D.insL G hG C w).u = fromRows D.u w := rfl
@[simp] theorem insL_x (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : (D.insL G hG C w).x = fromCols D.x 0 := rfl
@[simp] theorem insL_a (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : (D.insL G hG C w).a = D.a := rfl

end simps

omit [IsSylvesterDomain R] in
theorem whole_reindex (D : Display R n) (e : n ≃ m) :
    (D.reindex e).whole = D.whole.submatrix (e.symm.sumCongr (Equiv.refl Unit))
      (e.symm.sumCongr (Equiv.refl Unit)) := by
  ext (i | i) (j | j) <;> simp [whole]

omit [IsSylvesterDomain R] in
theorem isFull_whole_reindex (D : Display R n) (e : n ≃ m) :
    IsFull (D.reindex e).whole ↔ IsFull D.whole := by
  rw [whole_reindex, isFull_submatrix_equiv]

theorem whole_rmul (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    (D.rmul Q hQ f).whole = D.whole * fromBlocks Q f 0 1 := by
  simp [whole, fromBlocks_multiply, add_comm]

theorem isFull_whole_rmul (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q)
    (f : Matrix n Unit R) : IsFull (D.rmul Q hQ f).whole ↔ IsFull D.whole := by
  rw [whole_rmul, isFull_mul_right_iff (hQ.fromBlocks_upper isFull_one f)]

theorem whole_lmul (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    (D.lmul P hP h).whole = fromBlocks P 0 h 1 * D.whole := by
  simp [whole, fromBlocks_multiply, add_comm]

theorem isFull_whole_lmul (D : Display R n) (P : Matrix n n R) (hP : IsFull P)
    (h : Matrix Unit n R) : IsFull (D.lmul P hP h).whole ↔ IsFull D.whole := by
  rw [whole_lmul, isFull_mul_left_iff (hP.fromBlocks_lower isFull_one h)]

theorem whole_insU (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) :
    (D.insU G hG C p).whole.submatrix (sumRightComm n Unit g) (sumRightComm n Unit g) =
      fromBlocks D.whole (fromRows C p) 0 G := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [whole]

theorem isFull_whole_insU (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : IsFull (D.insU G hG C p).whole ↔ IsFull D.whole := by
  rw [← isFull_submatrix_equiv (sumRightComm n Unit g), whole_insU,
    isFull_fromBlocks_upper_iff hG]

theorem whole_insL (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) :
    (D.insL G hG C w).whole.submatrix (sumRightComm n Unit g) (sumRightComm n Unit g) =
      fromBlocks D.whole 0 (fromCols C w) G := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [whole]

theorem isFull_whole_insL (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : IsFull (D.insL G hG C w).whole ↔ IsFull D.whole := by
  rw [← isFull_submatrix_equiv (sumRightComm n Unit g), whole_insL,
    isFull_fromBlocks_lower_iff hG]

end Display

def Disp (R : Type) [Ring R] : Type := Σ k : ℕ, Display R (Fin k)

noncomputable def Display.toFin (D : Display R n) : Disp R :=
  ⟨Fintype.card n, D.reindex (Fintype.equivFin n)⟩

variable [IsSylvesterDomain R]

inductive Step : Disp R → Disp R → Prop
  | reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (e : n ≃ m) : Step D.toFin (D.reindex e).toFin
  | rmul {n : Type} [Fintype n] [DecidableEq n] (D : Display R n) (Q : Matrix n n R)
      (hQ : IsFull Q) (f : Matrix n Unit R) : Step D.toFin (D.rmul Q hQ f).toFin
  | lmul {n : Type} [Fintype n] [DecidableEq n] (D : Display R n) (P : Matrix n n R)
      (hP : IsFull P) (h : Matrix Unit n R) : Step D.toFin (D.lmul P hP h).toFin
  | insU {n g : Type} [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g] (D : Display R n)
      (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R) (p : Matrix Unit g R) :
      Step D.toFin (D.insU G hG C p).toFin
  | insL {n g : Type} [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g] (D : Display R n)
      (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R) (w : Matrix g Unit R) :
      Step D.toFin (D.insL G hG C w).toFin

def Loc (R : Type) [Ring R] [IsSylvesterDomain R] : Type := Quot (Step (R := R))

namespace Loc

noncomputable def mk (D : Display R n) : Loc R := Quot.mk _ D.toFin

theorem mk_reindex (D : Display R n) (e : n ≃ m) : mk (D.reindex e) = mk D :=
  (Quot.sound (Step.reindex D e)).symm

theorem mk_rmul (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R) :
    mk (D.rmul Q hQ f) = mk D :=
  (Quot.sound (Step.rmul D Q hQ f)).symm

theorem mk_lmul (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R) :
    mk (D.lmul P hP h) = mk D :=
  (Quot.sound (Step.lmul D P hP h)).symm

theorem mk_insU (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
    (p : Matrix Unit g R) : mk (D.insU G hG C p) = mk D :=
  (Quot.sound (Step.insU D G hG C p)).symm

theorem mk_insL (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
    (w : Matrix g Unit R) : mk (D.insL G hG C w) = mk D :=
  (Quot.sound (Step.insL D G hG C w)).symm

omit [IsSylvesterDomain R] in
theorem sigma_reindex_cast {k k' : ℕ} (h : k = k') (D : Display R (Fin k)) :
    (⟨k', D.reindex (finCongr h)⟩ : Disp R) = ⟨k, D⟩ := by
  subst h
  simp

theorem quot_mk_eq_mk {k : ℕ} (D : Display R (Fin k)) :
    (Quot.mk _ (⟨k, D⟩ : Disp R) : Loc R) = mk D := by
  have h : k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
  have h1 : (D.reindex ((finCongr h).trans (Fintype.equivFin (Fin k)).symm)).toFin = ⟨k, D⟩ := by
    rw [Display.toFin, Display.reindex_reindex, Equiv.trans_assoc, Equiv.symm_trans_self,
      Equiv.trans_refl]
    exact sigma_reindex_cast h D
  rw [← h1]
  exact mk_reindex D _

@[elab_as_elim]
theorem ind {P : Loc R → Prop}
    (h : ∀ (n : Type) [Fintype n] [DecidableEq n] (D : Display R n), P (mk D)) (z : Loc R) :
    P z := by
  induction z using Quot.ind with
  | mk s =>
    obtain ⟨k, D⟩ := s
    rw [quot_mk_eq_mk]
    exact h _ D

noncomputable def lift {β : Sort*}
    (F : ∀ (n : Type) [Fintype n] [DecidableEq n], Display R n → β)
    (h_reindex : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (e : n ≃ m), F m (D.reindex e) = F n D)
    (h_rmul : ∀ (n : Type) [Fintype n] [DecidableEq n] (D : Display R n) (Q : Matrix n n R)
      (hQ : IsFull Q) (f : Matrix n Unit R), F n (D.rmul Q hQ f) = F n D)
    (h_lmul : ∀ (n : Type) [Fintype n] [DecidableEq n] (D : Display R n) (P : Matrix n n R)
      (hP : IsFull P) (h : Matrix Unit n R), F n (D.lmul P hP h) = F n D)
    (h_insU : ∀ (n g : Type) [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g]
      (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix n g R)
      (p : Matrix Unit g R), F (n ⊕ g) (D.insU G hG C p) = F n D)
    (h_insL : ∀ (n g : Type) [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g]
      (D : Display R n) (G : Matrix g g R) (hG : IsFull G) (C : Matrix g n R)
      (w : Matrix g Unit R), F (n ⊕ g) (D.insL G hG C w) = F n D) : Loc R → β :=
  Quot.lift (fun s => F (Fin s.1) s.2) (by
    have key : ∀ (n : Type) [Fintype n] [DecidableEq n] (D : Display R n),
        F (Fin (Fintype.card n)) (D.reindex (Fintype.equivFin n)) = F n D :=
      fun n _ _ D => h_reindex _ _ D _
    intro s t h
    cases h with
    | reindex D e => exact (key _ D).trans ((key _ _).trans (h_reindex _ _ D e)).symm
    | rmul D Q hQ f => exact (key _ D).trans ((key _ _).trans (h_rmul _ D Q hQ f)).symm
    | lmul D P hP h => exact (key _ D).trans ((key _ _).trans (h_lmul _ D P hP h)).symm
    | insU D G hG C p => exact (key _ D).trans ((key _ _).trans (h_insU _ _ D G hG C p)).symm
    | insL D G hG C w => exact (key _ D).trans ((key _ _).trans (h_insL _ _ D G hG C w)).symm)

theorem lift_mk {β : Sort*}
    (F : ∀ (n : Type) [Fintype n] [DecidableEq n], Display R n → β)
    (h_reindex h_rmul h_lmul h_insU h_insL) (D : Display R n) :
    lift F h_reindex h_rmul h_lmul h_insU h_insL (mk D) = F n D :=
  h_reindex _ _ D _

noncomputable def lift₂ {β : Sort*}
    (F : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m],
      Display R n → Display R m → β)
    (l_reindex : ∀ (n n' m : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      [Fintype m] [DecidableEq m] (D : Display R n) (e : n ≃ n') (E : Display R m),
      F n' m (D.reindex e) E = F n m D E)
    (l_rmul : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q) (f : Matrix n Unit R)
      (E : Display R m), F n m (D.rmul Q hQ f) E = F n m D E)
    (l_lmul : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (P : Matrix n n R) (hP : IsFull P) (h : Matrix Unit n R)
      (E : Display R m), F n m (D.lmul P hP h) E = F n m D E)
    (l_insU : ∀ (n g m : Type) [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g]
      [Fintype m] [DecidableEq m] (D : Display R n) (G : Matrix g g R) (hG : IsFull G)
      (C : Matrix n g R) (p : Matrix Unit g R) (E : Display R m),
      F (n ⊕ g) m (D.insU G hG C p) E = F n m D E)
    (l_insL : ∀ (n g m : Type) [Fintype n] [DecidableEq n] [Fintype g] [DecidableEq g]
      [Fintype m] [DecidableEq m] (D : Display R n) (G : Matrix g g R) (hG : IsFull G)
      (C : Matrix g n R) (w : Matrix g Unit R) (E : Display R m),
      F (n ⊕ g) m (D.insL G hG C w) E = F n m D E)
    (r_reindex : ∀ (n m m' : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      [Fintype m'] [DecidableEq m'] (D : Display R n) (E : Display R m) (e : m ≃ m'),
      F n m' D (E.reindex e) = F n m D E)
    (r_rmul : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (E : Display R m) (Q : Matrix m m R) (hQ : IsFull Q)
      (f : Matrix m Unit R), F n m D (E.rmul Q hQ f) = F n m D E)
    (r_lmul : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (D : Display R n) (E : Display R m) (P : Matrix m m R) (hP : IsFull P)
      (h : Matrix Unit m R), F n m D (E.lmul P hP h) = F n m D E)
    (r_insU : ∀ (n m g : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      [Fintype g] [DecidableEq g] (D : Display R n) (E : Display R m) (G : Matrix g g R)
      (hG : IsFull G) (C : Matrix m g R) (p : Matrix Unit g R),
      F n (m ⊕ g) D (E.insU G hG C p) = F n m D E)
    (r_insL : ∀ (n m g : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      [Fintype g] [DecidableEq g] (D : Display R n) (E : Display R m) (G : Matrix g g R)
      (hG : IsFull G) (C : Matrix g m R) (w : Matrix g Unit R),
      F n (m ⊕ g) D (E.insL G hG C w) = F n m D E) : Loc R → Loc R → β :=
  fun z w => lift (fun n _ _ D => lift (fun m _ _ E => F n m D E)
      (fun _ _ _ _ _ _ E e => r_reindex _ _ _ D E e)
      (fun _ _ _ E Q hQ f => r_rmul _ _ D E Q hQ f)
      (fun _ _ _ E P hP h => r_lmul _ _ D E P hP h)
      (fun _ _ _ _ _ _ E G hG C p => r_insU _ _ _ D E G hG C p)
      (fun _ _ _ _ _ _ E G hG C w' => r_insL _ _ _ D E G hG C w') w)
    (fun _ _ _ _ _ _ D e => by
      induction w using Loc.ind with
      | h m E => rw [lift_mk, lift_mk]; exact l_reindex _ _ _ D e E)
    (fun _ _ _ D Q hQ f => by
      induction w using Loc.ind with
      | h m E => rw [lift_mk, lift_mk]; exact l_rmul _ _ D Q hQ f E)
    (fun _ _ _ D P hP h => by
      induction w using Loc.ind with
      | h m E => rw [lift_mk, lift_mk]; exact l_lmul _ _ D P hP h E)
    (fun _ _ _ _ _ _ D G hG C p => by
      induction w using Loc.ind with
      | h m E => rw [lift_mk, lift_mk]; exact l_insU _ _ _ D G hG C p E)
    (fun _ _ _ _ _ _ D G hG C w' => by
      induction w using Loc.ind with
      | h m E => rw [lift_mk, lift_mk]; exact l_insL _ _ _ D G hG C w' E)
    z

theorem lift₂_mk {β : Sort*}
    (F : ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m],
      Display R n → Display R m → β)
    (l_reindex l_rmul l_lmul l_insU l_insL r_reindex r_rmul r_lmul r_insU r_insL)
    (D : Display R n) (E : Display R m) :
    lift₂ F l_reindex l_rmul l_lmul l_insU l_insL r_reindex r_rmul r_lmul r_insU r_insL
      (mk D) (mk E) = F n m D E := by
  unfold lift₂
  rw [lift_mk, lift_mk]

noncomputable def WholeFull : Loc R → Prop :=
  lift (fun _ _ _ D => IsFull D.whole)
    (fun _ _ _ _ _ _ D e => propext (D.isFull_whole_reindex e))
    (fun _ _ _ D Q hQ f => propext (D.isFull_whole_rmul Q hQ f))
    (fun _ _ _ D P hP h => propext (D.isFull_whole_lmul P hP h))
    (fun _ _ _ _ _ _ D G hG C p => propext (D.isFull_whole_insU G hG C p))
    (fun _ _ _ _ _ _ D G hG C w => propext (D.isFull_whole_insL G hG C w))

theorem wholeFull_mk (D : Display R n) : WholeFull (mk D) ↔ IsFull D.whole := by
  rw [WholeFull, lift_mk]

end Loc

end FRD
