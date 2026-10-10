import FRD.Defs

open HahnSeries

namespace FRD.Laurent

variable {B : Type*}

def LB [Zero B] (n : ℤ) (P : HahnSeries ℤ B) : Prop := ∀ m : ℤ, m < n → P.coeff m = 0

section Ring
variable [Ring B]

theorem LB.mono {n m : ℤ} {P : HahnSeries ℤ B} (h : LB n P) (hmn : m ≤ n) : LB m P :=
  fun i hi => h i (lt_of_lt_of_le hi hmn)

theorem LB_zero (n : ℤ) : LB n (0 : HahnSeries ℤ B) := fun _ _ => coeff_zero

theorem LB.add {n : ℤ} {P Q : HahnSeries ℤ B} (hP : LB n P) (hQ : LB n Q) : LB n (P + Q) :=
  fun i hi => by rw [coeff_add, hP i hi, hQ i hi, add_zero]

theorem LB.neg {n : ℤ} {P : HahnSeries ℤ B} (hP : LB n P) : LB n (-P) :=
  fun i hi => by rw [coeff_neg, hP i hi, neg_zero]

theorem LB.sub {n : ℤ} {P Q : HahnSeries ℤ B} (hP : LB n P) (hQ : LB n Q) : LB n (P - Q) :=
  fun i hi => by rw [coeff_sub, hP i hi, hQ i hi, sub_zero]

theorem LB.mul {n m : ℤ} {P Q : HahnSeries ℤ B} (hP : LB n P) (hQ : LB m Q) :
    LB (n + m) (P * Q) := by
  intro a ha
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, h⟩ := hij
  by_cases h1 : ij.1 < n
  · rw [hP _ h1, zero_mul]
  · have h2 : ij.2 < m := by omega
    rw [hQ _ h2, mul_zero]

theorem coeff_mul_of_LB {n m : ℤ} {P Q : HahnSeries ℤ B} (hP : LB n P) (hQ : LB m Q) :
    (P * Q).coeff (n + m) = P.coeff n * Q.coeff m := by
  rw [coeff_mul]
  refine (Finset.sum_eq_single (n, m) ?_ ?_)
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨-, -, h⟩ := hij
    by_cases h1 : ij.1 < n
    · rw [hP _ h1, zero_mul]
    · have h2 : ij.2 < m := by
        by_contra h2
        apply hne
        ext <;> simp only <;> omega
      rw [hQ _ h2, mul_zero]
  · intro hnm
    rw [Finset.mem_antidiagonal] at hnm
    by_cases h1 : P.coeff n = 0
    · rw [h1, zero_mul]
    · by_cases h2 : Q.coeff m = 0
      · rw [h2, mul_zero]
      · exact absurd ⟨h1, h2, rfl⟩ hnm

theorem exists_LB (P : HahnSeries ℤ B) : ∃ n : ℤ, LB n P :=
  ⟨P.order, fun _ hm => coeff_eq_zero_of_lt_order hm⟩

theorem LB_order (P : HahnSeries ℤ B) : LB P.order P := fun _ hm => coeff_eq_zero_of_lt_order hm

theorem LB_single (n : ℤ) (c : B) : LB n (single n c) :=
  fun _ hm => coeff_single_of_ne (ne_of_lt hm)

theorem LB_C (c : B) : LB 0 (C c : HahnSeries ℤ B) := LB_single 0 c

theorem LB_one : LB 0 (1 : HahnSeries ℤ B) := LB_single 0 1

theorem coeff_C_mul (c : B) (P : HahnSeries ℤ B) (n : ℤ) : (C c * P).coeff n = c * P.coeff n :=
  coeff_single_zero_mul

theorem coeff_mul_C (c : B) (P : HahnSeries ℤ B) (n : ℤ) : (P * C c).coeff n = P.coeff n * c :=
  coeff_mul_single_zero

theorem coeff_single_one_mul (k : ℤ) (P : HahnSeries ℤ B) (n : ℤ) :
    (single k (1 : B) * P).coeff n = P.coeff (n - k) := by
  rw [coeff_single_mul, one_mul]

theorem coeff_mul_single_one (k : ℤ) (P : HahnSeries ℤ B) (n : ℤ) :
    (P * single k (1 : B)).coeff n = P.coeff (n - k) := by
  rw [coeff_mul_single, mul_one]

theorem single_one_mul_comm (k : ℤ) (P : HahnSeries ℤ B) :
    single k (1 : B) * P = P * single k (1 : B) := by
  ext n
  rw [coeff_single_one_mul, coeff_mul_single_one]

private theorem eq_zero_of_forall_LB {P : HahnSeries ℤ B} (h : ∀ N : ℕ, LB (N : ℤ) P) :
    P = 0 := by
  ext m
  rw [coeff_zero]
  exact h (m.toNat + 1) m (by push_cast; omega)

private theorem LB.pow {Z : HahnSeries ℤ B} (hZ : LB 1 Z) (r : ℕ) : LB (r : ℤ) (Z ^ r) := by
  induction r with
  | zero => simpa using (LB_one : LB 0 (1 : HahnSeries ℤ B))
  | succ r ih =>
    rw [pow_succ]
    have h := ih.mul hZ
    push_cast
    exact h

private noncomputable def geomCoeff (Z : HahnSeries ℤ B) (n : ℤ) : B :=
  ∑ r ∈ Finset.range (n.toNat + 1), (Z ^ r).coeff n

private theorem geomCoeff_eq_sum {Z : HahnSeries ℤ B} (hZ : LB 1 Z) {n : ℤ} {N : ℕ}
    (hn : n ≤ N) :
    geomCoeff Z n = ∑ r ∈ Finset.range (N + 1), (Z ^ r).coeff n := by
  unfold geomCoeff
  refine Finset.sum_subset ?_ ?_
  · intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  · intro r _ hr
    simp only [Finset.mem_range, not_lt] at hr
    exact LB.pow hZ r n (by omega)

private theorem geomCoeff_of_neg {Z : HahnSeries ℤ B} (hZ : LB 1 Z) {n : ℤ} (hn : n < 0) :
    geomCoeff Z n = 0 :=
  Finset.sum_eq_zero fun r _ => LB.pow hZ r n (by omega)

private noncomputable def geom (Z : HahnSeries ℤ B) (hZ : LB 1 Z) : HahnSeries ℤ B :=
  ofSuppBddBelow (geomCoeff Z) ⟨0, fun n hn => by
    by_contra h
    exact hn (geomCoeff_of_neg hZ (not_le.mp h))⟩

private theorem coeff_geom {Z : HahnSeries ℤ B} (hZ : LB 1 Z) (n : ℤ) :
    (geom Z hZ).coeff n = geomCoeff Z n := rfl

private theorem LB_geom_sub {Z : HahnSeries ℤ B} (hZ : LB 1 Z) (N : ℕ) :
    LB ((N : ℤ) + 1) (geom Z hZ - ∑ r ∈ Finset.range (N + 1), Z ^ r) := by
  intro m hm
  rw [coeff_sub, coeff_sum, coeff_geom, sub_eq_zero]
  exact geomCoeff_eq_sum hZ (by omega)

private theorem one_sub_mul_geom {Z : HahnSeries ℤ B} (hZ : LB 1 Z) :
    (1 - Z) * geom Z hZ = 1 := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_LB fun N => ?_
  have h1 : LB 0 (1 - Z) := LB_one.sub (hZ.mono zero_le_one)
  have h2 := h1.mul (LB_geom_sub hZ N)
  have h3 : (1 - Z) * geom Z hZ - 1 =
      (1 - Z) * (geom Z hZ - ∑ r ∈ Finset.range (N + 1), Z ^ r) - Z ^ (N + 1) := by
    rw [mul_sub, mul_neg_geom_sum]
    abel
  rw [h3]
  exact (h2.mono (by omega)).sub ((LB.pow hZ (N + 1)).mono (by push_cast; omega))

private theorem geom_mul_one_sub {Z : HahnSeries ℤ B} (hZ : LB 1 Z) :
    geom Z hZ * (1 - Z) = 1 := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_LB fun N => ?_
  have h1 : LB 0 (1 - Z) := LB_one.sub (hZ.mono zero_le_one)
  have h2 := (LB_geom_sub hZ N).mul h1
  have h3 : geom Z hZ * (1 - Z) - 1 =
      (geom Z hZ - ∑ r ∈ Finset.range (N + 1), Z ^ r) * (1 - Z) - Z ^ (N + 1) := by
    rw [sub_mul, geom_sum_mul_neg]
    abel
  rw [h3]
  exact (h2.mono (by omega)).sub ((LB.pow hZ (N + 1)).mono (by push_cast; omega))

private theorem isUnit_one_sub {Z : HahnSeries ℤ B} (hZ : LB 1 Z) : IsUnit (1 - Z) :=
  ⟨⟨1 - Z, geom Z hZ, one_sub_mul_geom hZ, geom_mul_one_sub hZ⟩, rfl⟩

end Ring

section DivisionRing
variable [DivisionRing B]

theorem isUnit_or_eq_zero (P : HahnSeries ℤ B) : IsUnit P ∨ P = 0 := by
  by_cases hP : P = 0
  · exact Or.inr hP
  left
  have hc0 : P.coeff P.order ≠ 0 := by rwa [Ne, coeff_order_eq_zero]
  let u : (HahnSeries ℤ B)ˣ :=
    ⟨C (P.coeff P.order)⁻¹, C (P.coeff P.order),
      by rw [← map_mul, inv_mul_cancel₀ hc0, map_one],
      by rw [← map_mul, mul_inv_cancel₀ hc0, map_one]⟩
  let v : (HahnSeries ℤ B)ˣ :=
    ⟨single (-P.order) 1, single P.order 1,
      by rw [single_mul_single, neg_add_cancel, mul_one]; rfl,
      by rw [single_mul_single, add_neg_cancel, mul_one]; rfl⟩
  have hQ : ∀ n, ((u : HahnSeries ℤ B) * ((v : HahnSeries ℤ B) * P)).coeff n =
      (P.coeff P.order)⁻¹ * P.coeff (n + P.order) := by
    intro n
    change (C (P.coeff P.order)⁻¹ * (single (-P.order) 1 * P)).coeff n = _
    rw [coeff_C_mul, coeff_single_one_mul, sub_neg_eq_add]
  have hZ : LB 1 (1 - (u : HahnSeries ℤ B) * ((v : HahnSeries ℤ B) * P)) := by
    intro m hm
    rw [coeff_sub, hQ, coeff_one]
    rcases lt_or_eq_of_le (show m ≤ 0 by omega) with h | h
    · rw [if_neg (ne_of_lt h), LB_order P (m + P.order) (by omega), mul_zero, sub_zero]
    · subst h
      rw [if_pos rfl, zero_add, inv_mul_cancel₀ hc0, sub_self]
  have h := isUnit_one_sub hZ
  rw [sub_sub_cancel] at h
  rwa [Units.isUnit_units_mul, Units.isUnit_units_mul] at h

noncomputable instance instDivisionRing : DivisionRing (HahnSeries ℤ B) :=
  DivisionRing.ofIsUnitOrEqZero isUnit_or_eq_zero

theorem LB_inv {P : HahnSeries ℤ B} {k : ℤ} (hP : LB k P) (hk : P.coeff k ≠ 0) :
    LB (-k) P⁻¹ := by
  have hP0 : P ≠ 0 := ne_zero_of_coeff_ne_zero hk
  have hI0 : P⁻¹ ≠ 0 := inv_ne_zero hP0
  have hc' : P⁻¹.coeff P⁻¹.order ≠ 0 := by rwa [Ne, coeff_order_eq_zero]
  have h := coeff_mul_of_LB hP (LB_order P⁻¹)
  rw [mul_inv_cancel₀ hP0, coeff_one] at h
  have hk' : k + P⁻¹.order = 0 := by
    by_contra hh
    rw [if_neg hh] at h
    exact mul_ne_zero hk hc' h.symm
  have he : P⁻¹.order = -k := by omega
  rw [← he]
  exact LB_order _

theorem LB_inv_sub_inv {P Q : HahnSeries ℤ B} {k m : ℤ} (hP : LB k P) (hPk : P.coeff k ≠ 0)
    (hQ : LB k Q) (hQk : Q.coeff k ≠ 0) (h : LB m (P - Q)) : LB (m - 2 * k) (P⁻¹ - Q⁻¹) := by
  have hP0 : P ≠ 0 := ne_zero_of_coeff_ne_zero hPk
  have hQ0 : Q ≠ 0 := ne_zero_of_coeff_ne_zero hQk
  have key : P⁻¹ - Q⁻¹ = P⁻¹ * (Q - P) * Q⁻¹ := by
    rw [mul_sub, sub_mul, inv_mul_cancel₀ hP0, mul_assoc, mul_inv_cancel₀ hQ0, one_mul, mul_one]
  have hQP : LB m (Q - P) := by
    have h' := h.neg
    rwa [neg_sub] at h'
  rw [key]
  exact (((LB_inv hP hPk).mul hQP).mul (LB_inv hQ hQk)).mono (by omega)

end DivisionRing

section Map
variable {B' : Type*} [Ring B] [Ring B']

noncomputable def mapHom (φ : B →+* B') : HahnSeries ℤ B →+* HahnSeries ℤ B' where
  toFun P := P.map φ
  map_one' := by
    ext n
    rw [map_coeff, coeff_one, coeff_one]
    split_ifs <;> simp
  map_mul' P Q := by
    have h := HahnSeries.map_mul (Γ := ℤ) (φ : B →ₙ+* B') (x := P) (y := Q)
    ext n
    exact congrArg (fun x : HahnSeries ℤ B' => x.coeff n) h
  map_zero' := by
    ext n
    rw [map_coeff, coeff_zero, coeff_zero, map_zero]
  map_add' P Q := by
    ext n
    rw [map_coeff, coeff_add, coeff_add, map_coeff, map_coeff, map_add]

@[simp] theorem mapHom_coeff (φ : B →+* B') (P : HahnSeries ℤ B) (n : ℤ) :
    (mapHom φ P).coeff n = φ (P.coeff n) := rfl

@[simp] theorem mapHom_C (φ : B →+* B') (c : B) : mapHom φ (C c) = C (φ c) := by
  ext n
  rw [mapHom_coeff, C_apply, C_apply, coeff_single, coeff_single]
  split_ifs <;> simp

@[simp] theorem mapHom_single (φ : B →+* B') (n : ℤ) (c : B) :
    mapHom φ (single n c) = single n (φ c) := by
  ext m
  rw [mapHom_coeff, coeff_single, coeff_single]
  split_ifs <;> simp

end Map

end FRD.Laurent
