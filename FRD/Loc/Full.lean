import FRD.Defs

namespace FRD

open Matrix

section Helpers
variable {α : Type*} {m n m₁ m₂ n₁ n₂ : Type*}

theorem fromRows_add_fromRows [Add α] (A₁ A₁' : Matrix m₁ n α) (A₂ A₂' : Matrix m₂ n α) :
    fromRows A₁ A₂ + fromRows A₁' A₂' = fromRows (A₁ + A₁') (A₂ + A₂') := by
  ext (i | i) j <;> simp

theorem fromCols_add_fromCols [Add α] (A₁ A₁' : Matrix m n₁ α) (A₂ A₂' : Matrix m n₂ α) :
    fromCols A₁ A₂ + fromCols A₁' A₂' = fromCols (A₁ + A₁') (A₂ + A₂') := by
  ext i (j | j) <;> simp

@[simp] theorem fromCols_submatrix_inl (A₁ : Matrix m n₁ α) (A₂ : Matrix m n₂ α) :
    (fromCols A₁ A₂).submatrix id Sum.inl = A₁ := by
  ext i j; simp

@[simp] theorem fromCols_submatrix_inr (A₁ : Matrix m n₁ α) (A₂ : Matrix m n₂ α) :
    (fromCols A₁ A₂).submatrix id Sum.inr = A₂ := by
  ext i j; simp

@[simp] theorem fromRows_submatrix_inl (A₁ : Matrix m₁ n α) (A₂ : Matrix m₂ n α) :
    (fromRows A₁ A₂).submatrix Sum.inl id = A₁ := by
  ext i j; simp

@[simp] theorem fromRows_submatrix_inr (A₁ : Matrix m₁ n α) (A₂ : Matrix m₂ n α) :
    (fromRows A₁ A₂).submatrix Sum.inr id = A₂ := by
  ext i j; simp

end Helpers

section Basic
variable {R : Type*} [Ring R]

theorem FactorsThrough.submatrix {m n m' n' : Type*} {A : Matrix m n R} {r : ℕ}
    (h : FactorsThrough A r) (f : m' → m) (g : n' → n) : FactorsThrough (A.submatrix f g) r := by
  obtain ⟨P, Q, rfl⟩ := h
  refine ⟨P.submatrix f id, Q.submatrix id g, ?_⟩
  ext i j
  simp [Matrix.mul_apply]

theorem FactorsThrough.mul_left {l m n : Type*} [Fintype m] {A : Matrix m n R} {r : ℕ}
    (h : FactorsThrough A r) (M : Matrix l m R) : FactorsThrough (M * A) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨M * P, Q, (Matrix.mul_assoc _ _ _).symm⟩

theorem FactorsThrough.mul_right {m n p : Type*} [Fintype n] {A : Matrix m n R} {r : ℕ}
    (h : FactorsThrough A r) (N : Matrix n p R) : FactorsThrough (A * N) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨P, Q * N, Matrix.mul_assoc _ _ _⟩

theorem factorsThrough_of_mul {m n k : Type*} [Fintype k] (P : Matrix m k R) (Q : Matrix k n R)
    {r : ℕ} (h : Fintype.card k ≤ r) : FactorsThrough (P * Q) r := by
  classical
  have hc : Fintype.card (k ⊕ Fin (r - Fintype.card k)) = r := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  let e : k ⊕ Fin (r - Fintype.card k) ≃ Fin r := Fintype.equivFinOfCardEq hc
  refine ⟨(fromCols P 0).submatrix id e.symm, (fromRows Q 0).submatrix e.symm id, ?_⟩
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_fromRows]
  simp

theorem FactorsThrough.mono {m n : Type*} {A : Matrix m n R} {r s : ℕ}
    (h : FactorsThrough A r) (hrs : r ≤ s) : FactorsThrough A s := by
  obtain ⟨P, Q, rfl⟩ := h
  exact factorsThrough_of_mul P Q (by simpa using hrs)

theorem factorsThrough_zero {m n : Type*} (r : ℕ) : FactorsThrough (0 : Matrix m n R) r :=
  ⟨0, 0, by simp⟩

theorem isFull_of_isEmpty {n : Type*} [Fintype n] [IsEmpty n] (A : Matrix n n R) : IsFull A :=
  fun r _ => by simp

theorem IsFull.reindex {n m : Type*} [Fintype n] [Fintype m] {A : Matrix n n R} (h : IsFull A)
    (e : n ≃ m) : IsFull (A.submatrix e.symm e.symm) := by
  intro r hr
  have h1 := hr.submatrix e e
  rw [Matrix.submatrix_submatrix] at h1
  simp only [Equiv.symm_comp_self, Matrix.submatrix_id_id] at h1
  rw [← Fintype.card_congr e]
  exact h r h1

theorem isFull_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m] {A : Matrix n n R}
    (e : m ≃ n) : IsFull (A.submatrix e e) ↔ IsFull A := by
  constructor
  · intro h
    have := h.reindex e
    simpa using this
  · intro h
    simpa using h.reindex e.symm

theorem IsFull.of_mul_right {n : Type*} [Fintype n] {A B : Matrix n n R} (h : IsFull (A * B)) :
    IsFull A :=
  fun r hr => h r (hr.mul_right B)

theorem IsFull.of_mul_left {n : Type*} [Fintype n] {A B : Matrix n n R} (h : IsFull (A * B)) :
    IsFull B :=
  fun r hr => h r (hr.mul_left A)

theorem isFull_iff_ne_zero_of_unique {n : Type*} [Fintype n] [Unique n] (a : Matrix n n R) :
    IsFull a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    have := h 0 (factorsThrough_zero 0)
    simp at this
  · rintro h r ⟨P, Q, rfl⟩
    rw [Fintype.card_unique]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (by ext i j; simp [Matrix.mul_apply]) h
    · exact hr

theorem IsFull.of_fromBlocks_upper {n g : Type*} [Fintype n] [Fintype g] [DecidableEq g]
    {A : Matrix n n R} {C : Matrix n g R} {G : Matrix g g R}
    (h : IsFull (fromBlocks A C 0 G)) : IsFull A := by
  rintro r ⟨P, Q, rfl⟩
  have h1 : FactorsThrough (fromBlocks P C 0 G * fromBlocks Q 0 0 (1 : Matrix g g R))
      (r + Fintype.card g) := factorsThrough_of_mul _ _ (by simp)
  have h2 : fromBlocks P C 0 G * fromBlocks Q 0 0 (1 : Matrix g g R) = fromBlocks (P * Q) C 0 G := by
    simp [fromBlocks_multiply]
  rw [h2] at h1
  have := h _ h1
  simp only [Fintype.card_sum] at this
  omega

theorem IsFull.of_fromBlocks_lower {n g : Type*} [Fintype n] [Fintype g] [DecidableEq g]
    {A : Matrix n n R} {C : Matrix g n R} {G : Matrix g g R}
    (h : IsFull (fromBlocks A 0 C G)) : IsFull A := by
  rintro r ⟨P, Q, rfl⟩
  have h1 : FactorsThrough (fromBlocks P 0 0 (1 : Matrix g g R) * fromBlocks Q 0 C G)
      (r + Fintype.card g) := factorsThrough_of_mul _ _ (by simp)
  have h2 : fromBlocks P 0 0 (1 : Matrix g g R) * fromBlocks Q 0 C G = fromBlocks (P * Q) 0 C G := by
    simp [fromBlocks_multiply]
  rw [h2] at h1
  have := h _ h1
  simp only [Fintype.card_sum] at this
  omega

end Basic

section Sylvester
variable {R : Type*} [Ring R] [IsSylvesterDomain R]

theorem nullity' {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] (A : Matrix m n R)
    (B : Matrix n p R) (h : A * B = 0) :
    ∃ r s : ℕ, r + s ≤ Fintype.card n ∧ FactorsThrough A r ∧ FactorsThrough B s := by
  classical
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let ep := Fintype.equivFin p
  have h0 : A.submatrix em.symm en.symm * B.submatrix en.symm ep.symm = 0 := by
    rw [Matrix.submatrix_mul_equiv, h]; simp
  obtain ⟨r, s, hrs, hr, hs⟩ := IsSylvesterDomain.nullity _ _ h0
  refine ⟨r, s, hrs, ?_, ?_⟩
  · simpa using hr.submatrix em en
  · simpa using hs.submatrix en ep

theorem IsFull.mul {n : Type*} [Fintype n] {A B : Matrix n n R} (hA : IsFull A) (hB : IsFull B) :
    IsFull (A * B) := by
  rintro r ⟨P, Q, hPQ⟩
  have h0 : fromCols A P * fromRows B (-Q) = 0 := by
    rw [fromCols_mul_fromRows, hPQ]; simp
  obtain ⟨s, t, hst, hs, ht⟩ := nullity' _ _ h0
  have h1 := hA s (by simpa using hs.submatrix id Sum.inl)
  have h2 := hB t (by simpa using ht.submatrix Sum.inl id)
  simp only [Fintype.card_sum, Fintype.card_fin] at hst
  omega

theorem IsFull.fromBlocks_upper {n g : Type*} [Fintype n] [Fintype g]
    {A : Matrix n n R} {G : Matrix g g R} (hA : IsFull A) (hG : IsFull G) (C : Matrix n g R) :
    IsFull (fromBlocks A C 0 G) := by
  rintro r ⟨P, Q, hPQ⟩
  rw [← fromRows_toRows P, ← fromCols_toCols Q, fromRows_mul_fromCols, fromBlocks_inj] at hPQ
  obtain ⟨h11, -, h21, h22⟩ := hPQ
  obtain ⟨s, t, hst, hs, ht⟩ := nullity' _ _ h21.symm
  have h1 := hG s (by rw [h22]; exact hs.mul_right _)
  have h2 := hA t (by rw [h11]; exact ht.mul_left _)
  simp only [Fintype.card_fin] at hst
  simp only [Fintype.card_sum]
  omega

theorem IsFull.fromBlocks_lower {n g : Type*} [Fintype n] [Fintype g]
    {A : Matrix n n R} {G : Matrix g g R} (hA : IsFull A) (hG : IsFull G) (C : Matrix g n R) :
    IsFull (fromBlocks A 0 C G) := by
  rintro r ⟨P, Q, hPQ⟩
  rw [← fromRows_toRows P, ← fromCols_toCols Q, fromRows_mul_fromCols, fromBlocks_inj] at hPQ
  obtain ⟨h11, h12, -, h22⟩ := hPQ
  obtain ⟨s, t, hst, hs, ht⟩ := nullity' _ _ h12.symm
  have h1 := hA s (by rw [h11]; exact hs.mul_right _)
  have h2 := hG t (by rw [h22]; exact ht.mul_left _)
  simp only [Fintype.card_fin] at hst
  simp only [Fintype.card_sum]
  omega

theorem isFull_fromBlocks_upper_iff {n g : Type*} [Fintype n] [Fintype g] [DecidableEq g]
    {A : Matrix n n R} {G : Matrix g g R} (hG : IsFull G) (C : Matrix n g R) :
    IsFull (fromBlocks A C 0 G) ↔ IsFull A :=
  ⟨fun h => h.of_fromBlocks_upper, fun h => h.fromBlocks_upper hG C⟩

theorem isFull_fromBlocks_lower_iff {n g : Type*} [Fintype n] [Fintype g] [DecidableEq g]
    {A : Matrix n n R} {G : Matrix g g R} (hG : IsFull G) (C : Matrix g n R) :
    IsFull (fromBlocks A 0 C G) ↔ IsFull A :=
  ⟨fun h => h.of_fromBlocks_lower, fun h => h.fromBlocks_lower hG C⟩

theorem isFull_one_fin : ∀ k : ℕ, IsFull (1 : Matrix (Fin k) (Fin k) R)
  | 0 => isFull_of_isEmpty _
  | k + 1 => by
    have := IsSylvesterDomain.nontrivial (R := R)
    have h1 : IsFull (1 : Matrix (Fin 1) (Fin 1) R) :=
      (isFull_iff_ne_zero_of_unique _).2 one_ne_zero
    have h2 := ((isFull_one_fin k).fromBlocks_upper h1 0).reindex finSumFinEquiv
    rwa [fromBlocks_one, Matrix.submatrix_one_equiv] at h2

theorem isFull_one {n : Type*} [Fintype n] [DecidableEq n] : IsFull (1 : Matrix n n R) := by
  have h := (isFull_one_fin (R := R) (Fintype.card n)).reindex (Fintype.equivFin n).symm
  rwa [Matrix.submatrix_one_equiv] at h

theorem IsFull.of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}
    (h : A * B = 1) : IsFull A :=
  IsFull.of_mul_right (B := B) (h ▸ isFull_one)

theorem IsFull.of_mul_eq_one' {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}
    (h : A * B = 1) : IsFull B :=
  IsFull.of_mul_left (A := A) (h ▸ isFull_one)

theorem isFull_mul_right_iff {n : Type*} [Fintype n] {A T : Matrix n n R} (hT : IsFull T) :
    IsFull (A * T) ↔ IsFull A :=
  ⟨fun h => h.of_mul_right, fun h => h.mul hT⟩

theorem isFull_mul_left_iff {n : Type*} [Fintype n] {A T : Matrix n n R} (hT : IsFull T) :
    IsFull (T * A) ↔ IsFull A :=
  ⟨fun h => h.of_mul_left, fun h => hT.mul h⟩

end Sylvester

end FRD
