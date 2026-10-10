import FRD.Defs

namespace FRD
namespace WordBasis

variable {B X R : Type*} [DivisionRing B] [Ring R] (wb : WordBasis B X R)

theorem coeff_word_mul_ι (u : List X) (c : B) :
    wb.coeff (wb.word u * wb.ι c) = Finsupp.single u c := by
  ext w
  by_cases h : u <+: w
  · obtain ⟨v, rfl⟩ := h
    rw [wb.coeff_word_mul, wb.coeff_ι]
    by_cases hv : v = []
    · subst hv; simp
    · rw [Finsupp.single_eq_of_ne hv, Finsupp.single_eq_of_ne]
      simpa using hv
  · rw [wb.coeff_word_mul_of_not_prefix _ _ _ h, Finsupp.single_eq_of_ne]
    rintro rfl
    exact h List.prefix_rfl

theorem coeff_word (u : List X) : wb.coeff (wb.word u) = Finsupp.single u 1 := by
  have h := wb.coeff_word_mul_ι u 1
  rwa [map_one, mul_one] at h

theorem coeff_eq_zero_iff {r : R} : wb.coeff r = 0 ↔ r = 0 :=
  map_eq_zero_iff wb.coeff wb.coeff_injective

noncomputable def ofCoeff (f : List X →₀ B) : R := f.sum fun v c => wb.word v * wb.ι c

theorem coeff_ofCoeff (f : List X →₀ B) : wb.coeff (wb.ofCoeff f) = f := by
  unfold ofCoeff
  rw [map_finsuppSum]
  simp only [coeff_word_mul_ι]
  exact Finsupp.sum_single f

theorem ofCoeff_coeff (r : R) : wb.ofCoeff (wb.coeff r) = r :=
  wb.coeff_injective (wb.coeff_ofCoeff _)

theorem induction_on_support {P : R → Prop} (r : R) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (h : ∀ u, wb.coeff r u ≠ 0 → P (wb.word u * wb.ι (wb.coeff r u))) : P r := by
  have key : P (wb.ofCoeff (wb.coeff r)) := by
    unfold ofCoeff Finsupp.sum
    refine Finset.sum_induction _ P hadd h0 ?_
    intro u hu
    exact h u (Finsupp.mem_support_iff.mp hu)
  rwa [wb.ofCoeff_coeff] at key

theorem exists_of_coeff_word_mul_ne_zero {u : List X} {x : R} {w : List X}
    (h : wb.coeff (wb.word u * x) w ≠ 0) : ∃ v, w = u ++ v ∧ wb.coeff x v ≠ 0 := by
  by_cases hp : u <+: w
  · obtain ⟨v, rfl⟩ := hp
    exact ⟨v, rfl, by rwa [wb.coeff_word_mul] at h⟩
  · exact absurd (wb.coeff_word_mul_of_not_prefix _ _ _ hp) h

def below (n : ℕ) : AddSubgroup R where
  carrier := {r | ∀ w, wb.coeff r w ≠ 0 → w.length < n}
  zero_mem' := by
    intro w hw
    simp at hw
  add_mem' := by
    intro a b ha hb w hw
    by_contra hlt
    apply hw
    have h1 : wb.coeff a w = 0 := by_contra fun h => hlt (ha w h)
    have h2 : wb.coeff b w = 0 := by_contra fun h => hlt (hb w h)
    rw [map_add, Finsupp.add_apply, h1, h2, add_zero]
  neg_mem' := by
    intro a ha w hw
    apply ha w
    intro h
    apply hw
    rw [map_neg, Finsupp.neg_apply, h, neg_zero]

theorem mem_below {r : R} {n : ℕ} :
    r ∈ wb.below n ↔ ∀ w, wb.coeff r w ≠ 0 → w.length < n := Iff.rfl

theorem below_mono {m n : ℕ} (h : m ≤ n) {r : R} (hr : r ∈ wb.below m) : r ∈ wb.below n :=
  fun w hw => (hr w hw).trans_le h

theorem mem_below_zero {r : R} : r ∈ wb.below 0 ↔ r = 0 := by
  constructor
  · intro h
    rw [← wb.coeff_eq_zero_iff]
    ext w
    by_contra hw
    exact Nat.not_lt_zero _ (h w hw)
  · rintro rfl
    exact zero_mem _

theorem ι_mul_mem_below {r : R} {n : ℕ} (c : B) (hr : r ∈ wb.below n) :
    wb.ι c * r ∈ wb.below n := by
  refine wb.induction_on_support (P := fun x => wb.ι c * x ∈ wb.below n) r (by simp)
    (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb) ?_
  intro u hu w hw
  rw [← mul_assoc, wb.coeff_mul_ι] at hw
  have h1 : wb.coeff (wb.ι c * wb.word u) w ≠ 0 := left_ne_zero_of_mul hw
  exact (wb.filtration c u w h1).trans_lt (hr u hu)

theorem mul_mem_below {r s : R} {m n k : ℕ} (hr : r ∈ wb.below m) (hs : s ∈ wb.below n)
    (hk : 0 < m → 0 < n → m + n ≤ k + 1) : r * s ∈ wb.below k := by
  refine wb.induction_on_support (P := fun x => x * s ∈ wb.below k) r (by simp)
    (fun a b ha hb => by rw [add_mul]; exact add_mem ha hb) ?_
  intro u hu w hw
  rw [mul_assoc] at hw
  obtain ⟨v, rfl, hv⟩ := wb.exists_of_coeff_word_mul_ne_zero hw
  have h1 := hr u hu
  have h2 := wb.ι_mul_mem_below _ hs v hv
  rw [List.length_append]
  have h3 := hk (by omega) (by omega)
  omega

noncomputable def transd (w : List X) : R →+ R where
  toFun r := wb.ofCoeff
    (Finsupp.comapDomain (fun v => w ++ v) (wb.coeff r) (List.append_right_injective w).injOn)
  map_zero' := by
    apply wb.coeff_injective
    ext v
    simp [coeff_ofCoeff]
  map_add' a b := by
    apply wb.coeff_injective
    ext v
    simp [coeff_ofCoeff, Finsupp.comapDomain_apply]

theorem coeff_transd (w : List X) (r : R) (v : List X) :
    wb.coeff (wb.transd w r) v = wb.coeff r (w ++ v) := by
  change wb.coeff (wb.ofCoeff _) v = _
  rw [coeff_ofCoeff, Finsupp.comapDomain_apply]

theorem transd_mul_ι (w : List X) (r : R) (c : B) :
    wb.transd w (r * wb.ι c) = wb.transd w r * wb.ι c := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd, coeff_mul_ι, coeff_mul_ι, coeff_transd]

theorem transd_append_word_mul (w u' : List X) (r : R) :
    wb.transd w (wb.word (w ++ u') * r) = wb.word u' * r := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd]
  by_cases h : u' <+: v
  · obtain ⟨v', rfl⟩ := h
    rw [← List.append_assoc, coeff_word_mul, coeff_word_mul]
  · rw [wb.coeff_word_mul_of_not_prefix _ _ _ h, wb.coeff_word_mul_of_not_prefix]
    rwa [List.prefix_append_right_inj]

theorem transd_word_mul_append (u w'' : List X) (r : R) :
    wb.transd (u ++ w'') (wb.word u * r) = wb.transd w'' r := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd, coeff_transd, List.append_assoc, coeff_word_mul]

theorem transd_word_mul_of_not_prefix {u w : List X} (h1 : ¬ u <+: w) (h2 : ¬ w <+: u) (r : R) :
    wb.transd w (wb.word u * r) = 0 := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd, map_zero, Finsupp.zero_apply]
  apply wb.coeff_word_mul_of_not_prefix
  intro h
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append w v) with h | h
  · exact h1 h
  · exact h2 h

theorem transd_ι_of_ne_nil {w : List X} (hw : w ≠ []) (c : B) : wb.transd w (wb.ι c) = 0 := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd, coeff_ι, map_zero, Finsupp.zero_apply, Finsupp.single_eq_of_ne]
  simp [hw]

theorem transd_mem_below {r : R} {n : ℕ} (w : List X) (hr : r ∈ wb.below n) :
    wb.transd w r ∈ wb.below (n - w.length) := by
  intro v hv
  rw [coeff_transd] at hv
  have h := hr _ hv
  rw [List.length_append] at h
  omega

theorem transd_mul_sub_mem_below (w : List X) (f g : R) {n : ℕ} (hg : g ∈ wb.below (n + 1)) :
    wb.transd w (f * g) - wb.transd w f * g ∈ wb.below n := by
  refine wb.induction_on_support
    (P := fun x => wb.transd w (x * g) - wb.transd w x * g ∈ wb.below n) f (by simp) ?_ ?_
  · intro a b ha hb
    have h : wb.transd w ((a + b) * g) - wb.transd w (a + b) * g
        = (wb.transd w (a * g) - wb.transd w a * g)
          + (wb.transd w (b * g) - wb.transd w b * g) := by
      rw [add_mul, map_add, map_add, add_mul]
      abel
    rw [h]
    exact add_mem ha hb
  · intro u _
    generalize wb.coeff f u = c
    have hg' : wb.ι c * g ∈ wb.below (n + 1) := wb.ι_mul_mem_below c hg
    change wb.transd w (wb.word u * wb.ι c * g) - wb.transd w (wb.word u * wb.ι c) * g ∈ wb.below n
    rw [mul_assoc]
    by_cases h1 : w <+: u
    · obtain ⟨u', rfl⟩ := h1
      rw [transd_append_word_mul, transd_append_word_mul, mul_assoc, sub_self]
      exact zero_mem _
    · by_cases h2 : u <+: w
      · obtain ⟨w'', rfl⟩ := h2
        have hw'' : w'' ≠ [] := by
          rintro rfl
          exact h1 (by simp)
        rw [transd_word_mul_append, transd_word_mul_append, transd_ι_of_ne_nil _ hw'', zero_mul,
          sub_zero]
        refine wb.below_mono ?_ (wb.transd_mem_below w'' hg')
        have hpos : 0 < w''.length := List.length_pos_iff.mpr hw''
        omega
      · rw [transd_word_mul_of_not_prefix _ h2 h1, transd_word_mul_of_not_prefix _ h2 h1, zero_mul,
          sub_zero]
        exact zero_mem _

noncomputable def size (r : R) : ℕ := (wb.coeff r).support.sup fun w => w.length + 1

theorem size_le_iff {r : R} {n : ℕ} : wb.size r ≤ n ↔ r ∈ wb.below n := by
  unfold size
  rw [Finset.sup_le_iff]
  constructor
  · intro h w hw
    exact h w (Finsupp.mem_support_iff.mpr hw)
  · intro h w hw
    exact h w (Finsupp.mem_support_iff.mp hw)

theorem mem_below_size (r : R) : r ∈ wb.below (wb.size r) := wb.size_le_iff.mp le_rfl

theorem size_eq_zero_iff (r : R) : wb.size r = 0 ↔ r = 0 := by
  rw [← Nat.le_zero, size_le_iff, mem_below_zero]

theorem exists_coeff_ne_zero_of_ne_zero {r : R} (hr : r ≠ 0) :
    ∃ w, wb.coeff r w ≠ 0 ∧ wb.size r = w.length + 1 := by
  have hne : (wb.coeff r).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h => hr (wb.coeff_eq_zero_iff.mp h)
  obtain ⟨w, hw, h⟩ := Finset.exists_mem_eq_sup _ hne (fun w : List X => w.length + 1)
  exact ⟨w, Finsupp.mem_support_iff.mp hw, h⟩

theorem transd_eq_ι {r : R} {w : List X} (hw : wb.size r = w.length + 1) :
    wb.transd w r = wb.ι (wb.coeff r w) := by
  apply wb.coeff_injective
  ext v
  rw [coeff_transd, coeff_ι]
  by_cases hv : v = []
  · subst hv
    simp
  · rw [Finsupp.single_eq_of_ne hv]
    by_contra h
    have h1 := wb.mem_below_size r _ h
    rw [List.length_append, hw] at h1
    have hpos : 0 < v.length := List.length_pos_iff.mpr hv
    omega

theorem depReducing : DepReducing R wb.size where
  size_eq_zero := wb.size_eq_zero_iff
  reduce := by
    classical
    intro ι s a b hsum hex hb
    let key : ι → ℕ ×ₗ ℕ := fun i => toLex (wb.size (a i) + wb.size (b i), wb.size (b i))
    have hs' : (s.filter fun i => a i ≠ 0).Nonempty := by
      obtain ⟨i, hi, hai⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ key hs'
    rw [Finset.mem_filter] at hm
    obtain ⟨hms, ham⟩ := hm
    obtain ⟨w, hw, hsz⟩ := wb.exists_coeff_ne_zero_of_ne_zero ham
    have hTm : wb.transd w (a m) = wb.ι (wb.coeff (a m) w) := wb.transd_eq_ι hsz
    have hpos : ∀ i ∈ s, 0 < wb.size (b i) := fun i hi =>
      Nat.pos_of_ne_zero fun h => hb i hi ((wb.size_eq_zero_iff _).mp h)
    have hbm := hpos m hms

    have claim : ∀ i ∈ s, wb.transd w (a i * b i) - wb.transd w (a i) * b i
        ∈ wb.below (wb.size (b m) - 1) := by
      intro i hi
      by_cases hai : a i = 0
      · rw [hai]
        simp
      have hle := hmax i (Finset.mem_filter.mpr ⟨hi, hai⟩)
      rw [Prod.Lex.le_iff] at hle
      simp only [key, ofLex_toLex] at hle
      have hbi := hpos i hi
      rcases hle with hlt | ⟨heq, hle2⟩
      · refine sub_mem ?_ ?_
        · have h1 : a i * b i ∈ wb.below (wb.size (a i) + wb.size (b i) - 1) :=
            wb.mul_mem_below (wb.mem_below_size _) (wb.mem_below_size _) (by omega)
          refine wb.below_mono ?_ (wb.transd_mem_below w h1)
          omega
        · exact wb.mul_mem_below (wb.transd_mem_below w (wb.mem_below_size (a i)))
            (wb.mem_below_size (b i)) (by omega)
      · have h1 : b i ∈ wb.below (wb.size (b i) - 1 + 1) := by
          rw [Nat.sub_add_cancel hbi]
          exact wb.mem_below_size _
        exact wb.below_mono (by omega) (wb.transd_mul_sub_mem_below w (a i) (b i) h1)
    have hsumT : ∑ i ∈ s, wb.transd w (a i) * b i ∈ wb.below (wb.size (b m) - 1) := by
      have h2 := sum_mem claim
      rw [Finset.sum_sub_distrib, ← map_sum, hsum, map_zero, zero_sub] at h2
      exact neg_mem_iff.mp h2
    refine ⟨m, hms, fun i => if i = m then 0 else -(wb.ι (wb.coeff (a m) w)⁻¹ * wb.transd w (a i)),
      if_pos rfl, ?_⟩
    have heq : b m - ∑ i ∈ s,
        (if i = m then 0 else -(wb.ι (wb.coeff (a m) w)⁻¹ * wb.transd w (a i))) * b i
        = wb.ι (wb.coeff (a m) w)⁻¹ * ∑ i ∈ s, wb.transd w (a i) * b i := by
      have hbm' : b m = ∑ i ∈ s, (if i = m then b i else 0) := by
        rw [Finset.sum_ite_eq' s m b, if_pos hms]
      conv_lhs => rw [hbm']
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases him : i = m
      · rw [if_pos him, if_pos him, zero_mul, sub_zero, him, hTm, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hw, map_one, one_mul]
      · rw [if_neg him, if_neg him, zero_sub, neg_mul, neg_neg, mul_assoc]
    rw [heq]
    have h3 := wb.size_le_iff.mpr (wb.ι_mul_mem_below (wb.coeff (a m) w)⁻¹ hsumT)
    omega

end WordBasis
end FRD
