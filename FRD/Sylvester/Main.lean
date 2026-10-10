import FRD.Defs

namespace FRD

namespace Sylvester

section FactorsThrough

variable {R : Type*} [Ring R]

theorem factorsThrough_of_eq_mul {m n k : Type*} [Fintype k] {A : Matrix m n R}
    (P : Matrix m k R) (Q : Matrix k n R) (hA : A = P * Q) :
    FactorsThrough A (Fintype.card k) := by
  classical
  refine ⟨P.submatrix id (Fintype.equivFin k).symm, Q.submatrix (Fintype.equivFin k).symm id, ?_⟩
  rw [Matrix.submatrix_mul_equiv, hA, Matrix.submatrix_id_id]

theorem factorsThrough_card_cols {m n : Type*} [Fintype n] (A : Matrix m n R) :
    FactorsThrough A (Fintype.card n) := by
  classical
  exact factorsThrough_of_eq_mul A 1 (Matrix.mul_one A).symm

theorem factorsThrough_zero_of_isEmpty {m n : Type*} [IsEmpty n] (A : Matrix m n R) :
    FactorsThrough A 0 :=
  ⟨fun _ k => k.elim0, fun k => k.elim0, by ext i j; exact isEmptyElim j⟩

theorem factorsThrough_mono {m n : Type*} {A : Matrix m n R} {r r' : ℕ}
    (h : FactorsThrough A r) (hrr' : r ≤ r') : FactorsThrough A r' := by
  obtain ⟨P, Q, hPQ⟩ := h
  let P' : Matrix m (Fin r ⊕ Fin (r' - r)) R := Matrix.of fun i x =>
    Sum.elim (fun k => P i k) (fun _ => 0) x
  let Q' : Matrix (Fin r ⊕ Fin (r' - r)) n R := Matrix.of fun x j =>
    Sum.elim (fun k => Q k j) (fun _ => 0) x
  have key : A = P' * Q' := by
    ext i j
    rw [hPQ, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [P', Q']
  have := factorsThrough_of_eq_mul P' Q' key
  rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.add_sub_cancel' hrr'] at this

theorem factorsThrough_mul_right {m n p : Type*} [Fintype n] {A : Matrix m n R} {r : ℕ}
    (h : FactorsThrough A r) (C : Matrix n p R) : FactorsThrough (A * C) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨P, Q * C, Matrix.mul_assoc P Q C⟩

theorem factorsThrough_mul_left {l m n : Type*} [Fintype m] {A : Matrix m n R} {r : ℕ}
    (h : FactorsThrough A r) (C : Matrix l m R) : FactorsThrough (C * A) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨C * P, Q, (Matrix.mul_assoc C P Q).symm⟩

theorem factorsThrough_of_submatrix_cols {m n n' : Type*} {A : Matrix m n R} {r : ℕ}
    {f : n' → n} (hf : Function.Injective f) (hA : ∀ i, (¬ ∃ j, f j = i) → ∀ a, A a i = 0)
    (h : FactorsThrough (A.submatrix id f) r) : FactorsThrough A r := by
  obtain ⟨U, V, hUV⟩ := h
  refine ⟨U, Matrix.of fun k i => Function.extend f (fun j => V k j) 0 i, ?_⟩
  ext a i
  rw [Matrix.mul_apply]
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := hi
    have := congrFun (congrFun hUV a) j
    rw [Matrix.mul_apply] at this
    simpa [hf.extend_apply] using this
  · rw [hA i hi a]
    simp [Function.extend_apply' _ _ _ hi]

theorem factorsThrough_of_submatrix_rows {n p : Type*} [Fintype n] {B : Matrix n p R} {s : ℕ}
    (q : n → Prop) [DecidablePred q]
    (h : FactorsThrough (B.submatrix (Subtype.val : {i // q i} → n) id) s) :
    FactorsThrough B (s + Fintype.card {i // ¬ q i}) := by
  classical
  obtain ⟨U, V, hUV⟩ := h
  let U' : Matrix n (Fin s ⊕ {i // ¬ q i}) R := Matrix.of fun i x =>
    Sum.elim (fun k => if hi : q i then U ⟨i, hi⟩ k else 0) (fun j => if i = j.1 then 1 else 0) x
  let V' : Matrix (Fin s ⊕ {i // ¬ q i}) p R := Matrix.of fun x c =>
    Sum.elim (fun k => V k c) (fun j => B j.1 c) x
  have key : B = U' * V' := by
    ext i c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    by_cases hi : q i
    · have h1 := congrFun (congrFun hUV ⟨i, hi⟩) c
      rw [Matrix.mul_apply] at h1
      have h2 : ∀ j : {i // ¬ q i}, i ≠ j.1 := fun j hj => j.2 (hj ▸ hi)
      simpa [U', V', hi, h2] using h1
    · have h2 : ∀ j : {i // ¬ q i}, (if i = j.1 then (1 : R) else 0) * B j.1 c
          = if j = ⟨i, hi⟩ then B i c else 0 := by
        intro j
        by_cases hj : j = ⟨i, hi⟩
        · subst hj; simp
        · have : i ≠ j.1 := fun h => hj (Subtype.ext h.symm)
          simp [hj, this]
      simp [U', V', hi, h2]
  have := factorsThrough_of_eq_mul U' V' key
  simpa [Fintype.card_sum] using this

end FactorsThrough

section Trivialize

variable {R : Type*} [Ring R] {μ : R → ℕ}

theorem exists_trivializing (h : DepReducing R μ) {m : Type*} {n : Type} [Fintype n]
    [DecidableEq n] (X : Matrix m n R) (y : n → R) (hXy : X.mulVec y = 0) :
    ∃ P P' : Matrix n n R, P * P' = 1 ∧ P' * P = 1 ∧
      ∀ i, (P'.mulVec y) i = 0 ∨ ∀ a, (X * P) a i = 0 := by
  classical
  induction hk : ∑ i, μ (y i) using Nat.strong_induction_on generalizing X y with
  | _ k ih =>
    subst hk
    let I : Finset n := Finset.univ.filter (fun i => (∃ a, X a i ≠ 0) ∧ y i ≠ 0)
    have hI_mem : ∀ i, i ∈ I ↔ (∃ a, X a i ≠ 0) ∧ y i ≠ 0 := fun i => by simp [I]
    by_cases hI : I = ∅
    ·
      refine ⟨1, 1, by simp, by simp, fun i => ?_⟩
      have hi : i ∉ I := by simp [hI]
      rw [hI_mem, not_and_or] at hi
      rcases hi with h1 | h1
      · right
        intro a
        rw [Matrix.mul_one]
        by_contra hne
        exact h1 ⟨a, hne⟩
      · left
        rw [Matrix.one_mulVec]
        exact not_not.mp h1
    · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hI
      obtain ⟨⟨ρ, hρ⟩, -⟩ := (hI_mem i₀).mp hi₀

      have hsum : ∑ i ∈ I, X ρ i * y i = 0 := by
        have h0 : ∑ i, X ρ i * y i = 0 := by
          have := congrFun hXy ρ
          simpa [Matrix.mulVec, dotProduct] using this
        rw [← h0]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        rw [hI_mem, not_and_or] at hi
        rcases hi with h1 | h1
        · have : X ρ i = 0 := by
            by_contra hne
            exact h1 ⟨ρ, hne⟩
          rw [this, zero_mul]
        · rw [not_not.mp h1, mul_zero]
      obtain ⟨m₀, -, c, hcm, hlt⟩ :=
        h.reduce I (X ρ) y hsum ⟨i₀, hi₀, hρ⟩ (fun i hi => ((hI_mem i).mp hi).2)

      let c' : n → R := fun i => if i ∈ I then c i else 0
      have hc'm : c' m₀ = 0 := by simp [c', hcm]
      let N : Matrix n n R := Matrix.of fun i j => if i = m₀ then c' j else 0
      have hNN : N * N = 0 := by
        ext i k
        simp [N, Matrix.mul_apply, hc'm]
      have h1 : (1 + N) * (1 - N) = 1 := by
        rw [mul_sub, mul_one, add_mul, one_mul, hNN]; abel
      have h2 : (1 - N) * (1 + N) = 1 := by
        rw [mul_add, mul_one, sub_mul, one_mul, hNN]; abel
      have hNy : ∀ i, (N.mulVec y) i = if i = m₀ then ∑ j ∈ I, c j * y j else 0 := by
        intro i
        by_cases hi : i = m₀
        · simp [N, Matrix.mulVec, dotProduct, hi, c', ite_mul, Finset.sum_ite_mem]
        · simp [N, Matrix.mulVec, dotProduct, hi]
      let y' : n → R := (1 - N).mulVec y
      have hy' : ∀ i, y' i = if i = m₀ then y m₀ - ∑ j ∈ I, c j * y j else y i := by
        intro i
        simp only [y', Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hNy]
        split_ifs with hi
        · rw [hi]
        · rw [sub_zero]

      have hmeasure : ∑ i, μ (y' i) < ∑ i, μ (y i) := by
        apply Finset.sum_lt_sum
        · intro i _
          rw [hy']
          split_ifs with hi
          · rw [hi]; exact hlt.le
          · exact le_rfl
        · refine ⟨m₀, Finset.mem_univ _, ?_⟩
          rw [hy', if_pos rfl]
          exact hlt
      have hX'y' : (X * (1 + N)).mulVec y' = 0 := by
        simp only [y']
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, hXy]
      obtain ⟨Q, Q', hQQ', hQ'Q, hQ⟩ := ih _ hmeasure (X * (1 + N)) y' hX'y' rfl
      refine ⟨(1 + N) * Q, Q' * (1 - N), ?_, ?_, ?_⟩
      · calc (1 + N) * Q * (Q' * (1 - N)) = (1 + N) * (Q * Q') * (1 - N) := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hQQ', Matrix.mul_one, h1]
      · calc Q' * (1 - N) * ((1 + N) * Q) = Q' * ((1 - N) * (1 + N)) * Q := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h2, Matrix.mul_one, hQ'Q]
      · intro i
        have e1 : (Q' * (1 - N)).mulVec y = Q'.mulVec y' := by
          simp only [y']
          rw [Matrix.mulVec_mulVec]
        have e2 : X * ((1 + N) * Q) = X * (1 + N) * Q := (Matrix.mul_assoc _ _ _).symm
        rw [e1, e2]
        exact hQ i

end Trivialize

section Nullity

variable {R : Type*} [Ring R] {μ : R → ℕ}

theorem nullity_fin (h : DepReducing R μ) {m : Type*} :
    ∀ (p : ℕ) (n : Type) [Fintype n] [DecidableEq n] (A : Matrix m n R) (B : Matrix n (Fin p) R),
      A * B = 0 → ∃ r s : ℕ, r + s ≤ Fintype.card n ∧ FactorsThrough A r ∧ FactorsThrough B s := by
  intro p
  induction p with
  | zero =>
    intro n _ _ A B _
    exact ⟨Fintype.card n, 0, le_rfl, factorsThrough_card_cols A, factorsThrough_zero_of_isEmpty B⟩
  | succ p ih =>
    intro n _ _ A B hAB
    classical

    let y : n → R := fun i => B i 0
    have hAy : A.mulVec y = 0 := by
      ext a
      have := congrFun (congrFun hAB a) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, y] using this
    obtain ⟨P, P', hPP', hP'P, hP⟩ := exists_trivializing h A y hAy
    set A₁ : Matrix m n R := A * P with hA₁
    set B₁ : Matrix n (Fin (p + 1)) R := P' * B with hB₁
    have hA₁B₁ : A₁ * B₁ = 0 := by
      rw [hA₁, hB₁, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hAB]
    have hB₁0 : ∀ i, B₁ i 0 = (P'.mulVec y) i := by
      intro i
      simp [hB₁, Matrix.mul_apply, Matrix.mulVec, dotProduct, y]

    let q : n → Prop := fun i => (P'.mulVec y) i = 0
    have hcol : ∀ i, ¬ q i → ∀ a, A₁ a i = 0 := fun i hi => (hP i).resolve_left hi

    let A₂ : Matrix m {i // q i} R := A₁.submatrix id Subtype.val
    let B₂ : Matrix {i // q i} (Fin p) R := (B₁.submatrix Subtype.val id).submatrix id Fin.succ
    have hA₂B₂ : A₂ * B₂ = 0 := by
      ext a j
      have h0 := congrFun (congrFun hA₁B₁ a) j.succ
      rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype q] at h0
      have h1 : ∑ i : {i // ¬ q i}, A₁ a i * B₁ i j.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hcol i.1 i.2 a, zero_mul]
      rw [h1, add_zero] at h0
      simpa [A₂, B₂, Matrix.mul_apply] using h0
    obtain ⟨r, s, hrs, hr, hs⟩ := ih {i // q i} A₂ B₂ hA₂B₂

    have hA₁r : FactorsThrough A₁ r := by
      refine factorsThrough_of_submatrix_cols Subtype.val_injective ?_ hr
      intro i hi a
      exact hcol i (fun hqi => hi ⟨⟨i, hqi⟩, rfl⟩) a

    have hB₁s : FactorsThrough B₁ (s + Fintype.card {i // ¬ q i}) := by
      refine factorsThrough_of_submatrix_rows q ?_
      refine factorsThrough_of_submatrix_cols (Fin.succ_injective p) ?_ hs
      intro c hc i
      rw [Fin.exists_succ_eq, not_not] at hc
      subst hc
      simpa [hB₁0] using i.2
    have hA : A = A₁ * P' := by
      rw [hA₁, Matrix.mul_assoc, hPP', Matrix.mul_one]
    have hB : B = P * B₁ := by
      rw [hB₁, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
    refine ⟨r, s + Fintype.card {i // ¬ q i}, ?_, ?_, ?_⟩
    · have hcard : Fintype.card {i // q i} + Fintype.card {i // ¬ q i} = Fintype.card n := by
        rw [← Fintype.card_sum]
        exact Fintype.card_congr (Equiv.sumCompl q)
      omega
    · rw [hA]; exact factorsThrough_mul_right hA₁r P'
    · rw [hB]; exact factorsThrough_mul_left hB₁s P

theorem nullity (h : DepReducing R μ) {m : Type*} {n p : Type} [Fintype n] [Fintype p]
    (A : Matrix m n R) (B : Matrix n p R) (hAB : A * B = 0) :
    ∃ r s : ℕ, r + s ≤ Fintype.card n ∧ FactorsThrough A r ∧ FactorsThrough B s := by
  classical
  let e := Fintype.equivFin p
  have h0 : A * B.submatrix id e.symm = 0 := by
    have : A * B.submatrix id e.symm = (A * B).submatrix id e.symm := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, hAB]; rfl
  obtain ⟨r, s, hrs, hr, U, V, hUV⟩ := nullity_fin h _ n A (B.submatrix id e.symm) h0
  refine ⟨r, s, hrs, hr, U, V.submatrix id e, ?_⟩
  ext i j
  have := congrFun (congrFun hUV i) (e j)
  simpa [Matrix.mul_apply] using this

end Nullity

end Sylvester

theorem DepReducing.isSylvesterDomain {R : Type*} [Ring R] [Nontrivial R] {μ : R → ℕ}
    (h : DepReducing R μ) : IsSylvesterDomain R :=
  ⟨inferInstance, fun {_ n p} A B hAB => by
    simpa using Sylvester.nullity_fin h p (Fin n) A B hAB⟩

end FRD
