import FRD.Loc.Division

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace FRD

open Matrix

variable {R : Type} [Ring R] [IsSylvesterDomain R]
variable {n m l g : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype l] [DecidableEq l] [Fintype g] [DecidableEq g]

def rowE (R : Type) [Ring R] {n : Type} [DecidableEq n] (j : n) : Matrix Unit n R :=
  Matrix.of fun _ k => if j = k then 1 else 0

def colE (R : Type) [Ring R] {n : Type} [DecidableEq n] (k : n) : Matrix n Unit R :=
  Matrix.of fun i _ => if i = k then 1 else 0

omit [IsSylvesterDomain R] in
theorem rowE_mul_apply (i : n) (M : Matrix n m R) (a : Unit) (k : m) :
    (rowE R i * M) a k = M i k := by
  simp [rowE, Matrix.mul_apply]

omit [IsSylvesterDomain R] in
theorem eq_sum_rowE (x : Matrix Unit n R) :
    x = ∑ j, Matrix.scalar Unit (x () j) * rowE R j := by
  ext a k
  simp [rowE, Matrix.sum_apply, Matrix.mul_apply]

omit [IsSylvesterDomain R] in
theorem eq_scalar_unit (a : Matrix Unit Unit R) : a = Matrix.scalar Unit (a () ()) := by
  ext i j
  simp

namespace Display

theorem add_same_key (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R)
    (x y : Matrix Unit n R) (a b : Matrix Unit Unit R)
    (hQ : IsFull (fromBlocks (1 : Matrix n n R) 0 1 (1 : Matrix n n R)))
    (hP : IsFull (fromBlocks (1 : Matrix n n R) 0 (-1) (1 : Matrix n n R))) :
    (((⟨A, u, x, a, hA⟩ : Display R n).add ⟨A, u, y, b, hA⟩).rmul _ hQ 0).lmul _ hP 0 =
      (⟨A, u, x + y, a + b, hA⟩ : Display R n).insU A hA 0 y := by
  apply Display.ext <;> blk_simp

theorem scalar_mul_reindex (c : Matrix Unit Unit R) (D : Display R n) :
    ((scalar c).mul D).reindex (Equiv.emptySum Empty n) =
      ⟨D.A, D.u, c * D.x, c * D.a, D.full⟩ := by
  apply Display.ext
  · ext i j; simp
  · ext i j; simp
  · ext i j; simp
  · simp

theorem scalar_neg (c : Matrix Unit Unit R) : (scalar c).neg = scalar (-c) := by
  apply Display.ext <;> simp [scalar]

end Display

namespace Loc

open Display

theorem mk_add_same (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R)
    (x y : Matrix Unit n R) (a b : Matrix Unit Unit R) :
    mk (⟨A, u, x, a, hA⟩ : Display R n) + mk (⟨A, u, y, b, hA⟩ : Display R n) =
      mk (⟨A, u, x + y, a + b, hA⟩ : Display R n) := by
  have hQ : IsFull (fromBlocks (1 : Matrix n n R) 0 1 (1 : Matrix n n R)) :=
    isFull_one.fromBlocks_lower isFull_one _
  have hP : IsFull (fromBlocks (1 : Matrix n n R) 0 (-1) (1 : Matrix n n R)) :=
    isFull_one.fromBlocks_lower isFull_one _
  rw [mk_add_mk]
  calc mk ((⟨A, u, x, a, hA⟩ : Display R n).add ⟨A, u, y, b, hA⟩)
      = mk ((((⟨A, u, x, a, hA⟩ : Display R n).add ⟨A, u, y, b, hA⟩).rmul _ hQ 0).lmul _ hP 0) := by
        rw [mk_lmul, mk_rmul]
    _ = mk (⟨A, u, x + y, a + b, hA⟩ : Display R n) := by
        rw [add_same_key A hA u x y a b hQ hP, mk_insU]

theorem mk_scalar_mul_mk (c : Matrix Unit Unit R) (D : Display R n) :
    mk (scalar c) * mk D = mk (⟨D.A, D.u, c * D.x, c * D.a, D.full⟩ : Display R n) := by
  rw [mk_mul_mk, ← scalar_mul_reindex, mk_reindex]

theorem neg_mk_scalar (c : Matrix Unit Unit R) : -mk (scalar c) = mk (scalar (-c)) := by
  rw [neg_mk, scalar_neg]

theorem mk_scalar_eq_of (a : Matrix Unit Unit R) : mk (scalar a) = of (a () ()) := by
  rw [of_apply, ← eq_scalar_unit]

noncomputable def Phi (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R) :
    Matrix Unit n R →+ Loc R where
  toFun x := mk (⟨A, u, x, 0, hA⟩ : Display R n)
  map_zero' := by rw [mk_of_x_eq_zero _ rfl]; rfl
  map_add' x y := by rw [mk_add_same]; simp

theorem Phi_apply (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R) (x : Matrix Unit n R) :
    Phi A hA u x = mk (⟨A, u, x, 0, hA⟩ : Display R n) := rfl

theorem Phi_scalar_mul (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R)
    (c : Matrix Unit Unit R) (x : Matrix Unit n R) :
    Phi A hA u (c * x) = mk (scalar c) * Phi A hA u x := by
  rw [Phi_apply, Phi_apply, mk_scalar_mul_mk]
  simp

theorem Phi_mul_A (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R)
    (h : Matrix Unit n R) : Phi A hA u (h * A) = -mk (scalar (h * u)) := by
  have h1 : mk ((⟨A, u, h * A, 0, hA⟩ : Display R n).lmul 1 isFull_one (-h)) =
      mk (scalar (-(h * u))) := by
    rw [mk_of_x_eq_zero _ (by simp)]
    simp
  rw [Phi_apply, neg_mk_scalar, ← h1, mk_lmul]

theorem mk_eq_scalar_add_Phi (D : Display R n) :
    mk D = mk (scalar D.a) + Phi D.A D.full D.u D.x := by
  have h1 : mk (scalar D.a) = mk (⟨D.A, D.u, 0, D.a, D.full⟩ : Display R n) :=
    (mk_of_x_eq_zero (⟨D.A, D.u, 0, D.a, D.full⟩ : Display R n) rfl).symm
  rw [h1, Phi_apply, mk_add_same]
  congr 1
  apply Display.ext <;> simp

theorem Phi_eq_sum (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R)
    (x : Matrix Unit n R) : Phi A hA u x = ∑ j, of (x () j) * Phi A hA u (rowE R j) := by
  conv_lhs => rw [eq_sum_rowE x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Phi_scalar_mul]
  rfl

theorem sum_of_mul_Phi_rowE (A : Matrix n n R) (hA : IsFull A) (u : Matrix n Unit R) (i : n) :
    ∑ j, of (A i j) * Phi A hA u (rowE R j) = -of (u i ()) := by
  have h1 := Phi_eq_sum A hA u (rowE R i * A)
  rw [Phi_mul_A, mk_scalar_eq_of] at h1
  simp only [rowE_mul_apply] at h1
  exact h1.symm

theorem isUnit_map_of (A : Matrix n n R) (hA : IsFull A) :
    IsUnit (A.map (of : R →+* Loc R)) := by
  let Θ : Matrix n n (Loc R) := Matrix.of fun j k => -Phi A hA (colE R k) (rowE R j)
  have h1 : A.map (of : R →+* Loc R) * Θ = 1 := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.map_apply, Θ, Matrix.of_apply, mul_neg,
      Finset.sum_neg_distrib, sum_of_mul_Phi_rowE, neg_neg, colE, Matrix.one_apply]
    split_ifs <;> simp
  exact isUnit_iff_exists.2 ⟨Θ, h1, mul_eq_one_comm.1 h1⟩

end Loc

end FRD
