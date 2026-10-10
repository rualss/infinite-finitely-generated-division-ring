import FRD.Loc.Honest

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace FRD

open Matrix

variable {R : Type} [Ring R] [IsSylvesterDomain R]
variable {S : Type} [Ring S]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

def Inverts (f : R →+* S) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n R), IsFull A → IsUnit (A.map f)

omit [IsSylvesterDomain R] in
theorem inverts_of_fin (f : R →+* S)
    (hf : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), IsFull A → IsUnit (A.map f)) :
    Inverts f := by
  intro n _ _ A hA
  let e := Fintype.equivFin n
  obtain ⟨B, h1, h2⟩ := isUnit_iff_exists.1 (hf _ _ (hA.reindex e))
  have hA' : A.map f = ((A.submatrix e.symm e.symm).map f).submatrix e e := by
    ext i j; simp
  refine isUnit_iff_exists.2 ⟨B.submatrix e e, ?_, ?_⟩
  · rw [hA', Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  · rw [hA', Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv]

section mapLemmas
variable {a b c : Type*} [Fintype b] (f : R →+* S)

omit [IsSylvesterDomain R] in
theorem mapf_mul (M : Matrix a b R) (N : Matrix b c R) : (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul

omit [IsSylvesterDomain R] [Fintype b] in
theorem mapf_add (M N : Matrix a b R) : (M + N).map f = M.map f + N.map f :=
  Matrix.map_add f (map_add f) M N

omit [IsSylvesterDomain R] [Fintype b] in
theorem mapf_neg (M : Matrix a b R) : (-M).map f = -M.map f :=
  Matrix.map_neg f (map_neg f) M

omit [IsSylvesterDomain R] [Fintype b] in
theorem mapf_zero : (0 : Matrix a b R).map f = 0 :=
  Matrix.map_zero f (map_zero f)

end mapLemmas

namespace Display

noncomputable def sol (f : R →+* S) (D : Display R n) : Matrix n Unit S :=
  Ring.inverse (D.A.map f) * D.u.map f

noncomputable def val (f : R →+* S) (D : Display R n) : Matrix Unit Unit S :=
  D.a.map f - D.x.map f * D.sol f

variable {f : R →+* S}

omit [IsSylvesterDomain R] in
theorem mul_sol (hf : Inverts f) (D : Display R n) : D.A.map f * D.sol f = D.u.map f := by
  rw [sol, ← Matrix.mul_assoc, Ring.mul_inverse_cancel _ (hf _ _ D.full), Matrix.one_mul]

omit [IsSylvesterDomain R] in
theorem val_eq_of_solution (hf : Inverts f) (D : Display R n) (W : Matrix n Unit S)
    (hW : D.A.map f * W = D.u.map f) : D.val f = D.a.map f - D.x.map f * W := by
  have h1 : D.sol f = W := by
    rw [sol, ← hW, ← Matrix.mul_assoc, Ring.inverse_mul_cancel _ (hf _ _ D.full), Matrix.one_mul]
  rw [val, h1]

omit [IsSylvesterDomain R] in
theorem val_reindex (hf : Inverts f) (D : Display R n) (e : n ≃ m) :
    (D.reindex e).val f = D.val f := by
  rw [val_eq_of_solution hf (D.reindex e) ((D.sol f).submatrix e.symm id) ?_, val]
  · simp only [reindex_a, reindex_x, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  · simp only [reindex_A, reindex_u, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      mul_sol hf]

theorem val_rmul (hf : Inverts f) (D : Display R n) (Q : Matrix n n R) (hQ : IsFull Q)
    (f₀ : Matrix n Unit R) : (D.rmul Q hQ f₀).val f = D.val f := by
  have hQ' := hf _ Q hQ
  have hW := D.mul_sol hf
  have key : ∀ M : Matrix n Unit S, Q.map f * (Ring.inverse (Q.map f) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hQ', Matrix.one_mul]
  rw [val_eq_of_solution hf (D.rmul Q hQ f₀) (Ring.inverse (Q.map f) * (D.sol f + f₀.map f)) ?_,
    val]
  · simp only [rmul_a, rmul_x, mapf_mul, mapf_add, Matrix.mul_assoc, key, Matrix.mul_add]
    abel
  · simp only [rmul_A, rmul_u, mapf_mul, mapf_add, Matrix.mul_assoc, key, Matrix.mul_add, hW]

theorem val_lmul (hf : Inverts f) (D : Display R n) (P : Matrix n n R) (hP : IsFull P)
    (h : Matrix Unit n R) : (D.lmul P hP h).val f = D.val f := by
  have hW := D.mul_sol hf
  rw [val_eq_of_solution hf (D.lmul P hP h) (D.sol f) ?_, val]
  · simp only [lmul_a, lmul_x, mapf_mul, mapf_add, Matrix.mul_assoc, Matrix.add_mul, hW]
    abel
  · simp only [lmul_A, lmul_u, mapf_mul, Matrix.mul_assoc, hW]

theorem val_insU (hf : Inverts f) (D : Display R n) (G : Matrix g g R) (hG : IsFull G)
    (C : Matrix n g R) (p : Matrix Unit g R) : (D.insU G hG C p).val f = D.val f := by
  have hW := D.mul_sol hf
  rw [val_eq_of_solution hf (D.insU G hG C p) (fromRows (D.sol f) 0) ?_, val]
  · simp [fromCols_map, fromCols_mul_fromRows]
  · simp [fromBlocks_map, fromRows_map, fromBlocks_mul_fromRows, hW, mapf_zero]

theorem val_insL (hf : Inverts f) (D : Display R n) (G : Matrix g g R) (hG : IsFull G)
    (C : Matrix g n R) (w : Matrix g Unit R) : (D.insL G hG C w).val f = D.val f := by
  have hG' := hf _ G hG
  have hW := D.mul_sol hf
  have key : ∀ M : Matrix g Unit S, G.map f * (Ring.inverse (G.map f) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hG', Matrix.one_mul]
  rw [val_eq_of_solution hf (D.insL G hG C w)
    (fromRows (D.sol f) (Ring.inverse (G.map f) * (w.map f - C.map f * D.sol f))) ?_, val]
  · simp [fromCols_map, fromCols_mul_fromRows, mapf_zero]
  · simp [fromBlocks_map, fromRows_map, fromBlocks_mul_fromRows, hW, mapf_zero, key]

omit [IsSylvesterDomain R] in
theorem val_scalar (a : Matrix Unit Unit R) : (scalar a).val f = a.map f := by
  simp [val, scalar, mapf_zero]

theorem val_add (hf : Inverts f) (D : Display R n) (E : Display R m) :
    (D.add E).val f = D.val f + E.val f := by
  have hW := D.mul_sol hf
  have hW' := E.mul_sol hf
  rw [val_eq_of_solution hf (D.add E) (fromRows (D.sol f) (E.sol f)) ?_, val, val]
  · simp only [add_a, add_x, mapf_add, fromCols_map, fromCols_mul_fromRows]
    abel
  · simp [fromBlocks_map, fromRows_map, fromBlocks_mul_fromRows, hW, hW', mapf_zero]

theorem val_mul (hf : Inverts f) (D : Display R n) (E : Display R m) :
    (D.mul E).val f = D.val f * E.val f := by
  have hW := D.mul_sol hf
  have hW' := E.mul_sol hf
  rw [val_eq_of_solution hf (D.mul E) (fromRows (D.sol f * E.val f) (E.sol f)) ?_]
  · simp only [mul_a, mul_x, mapf_mul, fromCols_map, fromCols_mul_fromRows, val, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  · simp only [mul_A, mul_u, fromBlocks_map, fromRows_map, fromBlocks_mul_fromRows, mapf_mul,
      mapf_zero, Matrix.zero_mul, zero_add, hW', ← Matrix.mul_assoc, hW]
    simp only [val, Matrix.mul_sub, Matrix.mul_assoc, sub_add_cancel]

theorem val_neg (hf : Inverts f) (D : Display R n) : D.neg.val f = -D.val f := by
  have hW := D.mul_sol hf
  rw [val_eq_of_solution hf D.neg (-D.sol f) ?_, val]
  · simp only [neg_a, neg_x, mapf_neg, Matrix.mul_neg]
    abel
  · simp only [neg_A, neg_u, mapf_neg, Matrix.mul_neg, hW]

end Display

namespace Loc

open Display

variable (f : R →+* S) (hf : Inverts f)

noncomputable def valM : Loc R → Matrix Unit Unit S :=
  lift (fun _ _ _ D => D.val f)
    (fun _ _ _ _ _ _ D e => D.val_reindex hf e)
    (fun _ _ _ D Q hQ f₀ => D.val_rmul hf Q hQ f₀)
    (fun _ _ _ D P hP h => D.val_lmul hf P hP h)
    (fun _ _ _ _ _ _ D G hG C p => D.val_insU hf G hG C p)
    (fun _ _ _ _ _ _ D G hG C w => D.val_insL hf G hG C w)

theorem valM_mk (D : Display R n) : valM f hf (mk D) = D.val f :=
  lift_mk _ _ _ _ _ _ D

noncomputable def liftHom : Loc R →+* S where
  toFun z := valM f hf z () ()
  map_one' := by
    rw [one_def, valM_mk, val_scalar]
    simp
  map_mul' a b := by
    induction a using Loc.ind with | h _ D => ?_
    induction b using Loc.ind with | h _ E => ?_
    rw [mk_mul_mk, valM_mk, valM_mk, valM_mk, val_mul hf]
    simp [Matrix.mul_apply]
  map_zero' := by
    rw [zero_def, valM_mk, val_scalar]
    simp
  map_add' a b := by
    induction a using Loc.ind with | h _ D => ?_
    induction b using Loc.ind with | h _ E => ?_
    rw [mk_add_mk, valM_mk, valM_mk, valM_mk, val_add hf]
    simp

theorem liftHom_comp_of : (liftHom f hf).comp of = f := by
  ext r
  change valM f hf (of r) () () = f r
  rw [of_apply, valM_mk, val_scalar]
  simp

theorem hom_ext' (g₁ g₂ : Loc R →+* S) (h : g₁.comp of = g₂.comp of) : g₁ = g₂ := by
  ext z
  induction z using Loc.ind with | h n D => ?_
  have h' : ∀ r : R, g₁ (of r) = g₂ (of r) := fun r => RingHom.congr_fun h r
  have formula : ∀ g : Loc R →+* S, g (mk D) =
      g (of (D.a () ())) + ∑ j, g (of (D.x () j)) * g (Phi D.A D.full D.u (rowE R j)) := by
    intro g
    rw [mk_eq_scalar_add_Phi, mk_scalar_eq_of, Phi_eq_sum, map_add, map_sum]
    simp only [map_mul]

  have hsys : ∀ g : Loc R →+* S,
      D.A.map (g.comp of) * (Matrix.of fun j (_ : Unit) => g (Phi D.A D.full D.u (rowE R j))) =
        (-D.u).map (g.comp of) := by
    intro g
    ext i ⟨⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply,
      Matrix.neg_apply]
    rw [map_neg of, ← sum_of_mul_Phi_rowE D.A D.full D.u i, map_sum]
    simp only [map_mul]
  have hU : IsUnit (D.A.map (g₁.comp of)) := by
    have h1 := (isUnit_map_of D.A D.full).map (g₁.mapMatrix (m := n))
    rwa [RingHom.mapMatrix_apply, Matrix.map_map] at h1
  obtain ⟨B, -, hB⟩ := isUnit_iff_exists.1 hU
  have hw : (Matrix.of fun j (_ : Unit) => g₁ (Phi D.A D.full D.u (rowE R j))) =
      (Matrix.of fun j (_ : Unit) => g₂ (Phi D.A D.full D.u (rowE R j))) := by
    have e1 := hsys g₁
    have e2 := hsys g₂
    rw [← h] at e2
    have e3 := congrArg (fun M => B * M) (e1.trans e2.symm)
    simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using e3
  have hw' : ∀ j, g₁ (Phi D.A D.full D.u (rowE R j)) = g₂ (Phi D.A D.full D.u (rowE R j)) :=
    fun j => congrFun (congrFun hw j) ()
  rw [formula g₁, formula g₂]
  simp only [h', hw']

end Loc

end FRD
