import FRD.Pointed.Operators

namespace FRD.Pointed

open MulOpposite

section Prepend

variable {B : Type*} [Ring B] {X : Type*}

theorem Pw_apply_append (u : List X) (g : NF B X) (w : List X) : Pw B u g (u ++ w) = g w := by
  rw [Pw_apply]
  exact Finsupp.mapDomain_apply (List.append_right_injective u) g w

theorem Pw_apply_of_not_prefix (u : List X) (g : NF B X) (w : List X) (h : ¬ u <+: w) :
    Pw B u g w = 0 := by
  rw [Pw_apply]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨w', rfl⟩
  exact h (List.prefix_append u w')

theorem Pw_apply_ne_zero {u : List X} {g : NF B X} {w : List X} (h : Pw B u g w ≠ 0) :
    ∃ w', w = u ++ w' ∧ g w' ≠ 0 := by
  by_cases hp : u <+: w
  · obtain ⟨w', rfl⟩ := hp
    exact ⟨w', rfl, by rwa [Pw_apply_append] at h⟩
  · exact absurd (Pw_apply_of_not_prefix u g w hp) h

end Prepend

section Filtration

variable {B : Type*} [Ring B] {X : Type*} {M : Type*} [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] (b : Module.Basis (Option X) Bᵐᵒᵖ M)

theorem Lam_length_le (u : List X) :
    ∀ (c : B) (w : List X), Lam b u c w ≠ 0 → w.length ≤ u.length := by
  induction u with
  | nil =>
    intro c w h
    rw [Lam_nil, Finsupp.single_apply] at h
    by_cases hw : [] = w
    · subst hw; simp
    · rw [if_neg hw] at h; exact absurd rfl h
  | cons x v ih =>
    intro c w h
    rw [Lam_cons, Finsupp.sum_apply] at h
    obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨w', rfl, hw'⟩ := Pw_apply_ne_zero ho
    have := ih _ _ hw'
    cases o <;> simp [Option.toList] <;> omega

end Filtration

section Ring

variable {B : Type*} [Ring B] {X : Type*} {M : Type*} [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M] (b : Module.Basis (Option X) Bᵐᵒᵖ M)
  (hone : ∀ c : B, c • b none = op c • b none)

noncomputable def PRing : Subring (Op B X) where
  carrier := {f | ell b (f (Finsupp.single [] 1)) = f}
  mul_mem' {f f'} hf hf' := by
    have hf₁ : ell b (f (Finsupp.single [] 1)) = f := hf
    have hf₂ : ell b (f' (Finsupp.single [] 1)) = f' := hf'
    show ell b ((f * f') (Finsupp.single [] 1)) = f * f'
    calc ell b ((f * f') (Finsupp.single [] 1))
        = ell b (ell b (f (Finsupp.single [] 1)) (f' (Finsupp.single [] 1))) := by
          rw [hf₁, Module.End.mul_apply]
      _ = ell b (f (Finsupp.single [] 1)) * ell b (f' (Finsupp.single [] 1)) :=
          (ell_mul_ell b hone _ _).symm
      _ = f * f' := by rw [hf₁, hf₂]
  one_mem' := by
    show ell b ((1 : Op B X) (Finsupp.single [] 1)) = 1
    simp
  add_mem' {f f'} hf hf' := by
    have hf₁ : ell b (f (Finsupp.single [] 1)) = f := hf
    have hf₂ : ell b (f' (Finsupp.single [] 1)) = f' := hf'
    show ell b ((f + f') (Finsupp.single [] 1)) = f + f'
    rw [LinearMap.add_apply, map_add, hf₁, hf₂]
  zero_mem' := by
    show ell b ((0 : Op B X) (Finsupp.single [] 1)) = 0
    simp
  neg_mem' {f} hf := by
    have hf₁ : ell b (f (Finsupp.single [] 1)) = f := hf
    show ell b ((-f) (Finsupp.single [] 1)) = -f
    rw [LinearMap.neg_apply, map_neg, hf₁]

theorem mem_PRing {f : Op B X} :
    f ∈ PRing b hone ↔ ell b (f (Finsupp.single [] 1)) = f := Iff.rfl

theorem ell_mem (g : NF B X) : ell b g ∈ PRing b hone := by
  rw [mem_PRing, ell_apply_nil]

theorem Lop_mem (a : B) : Lop b a ∈ PRing b hone := by
  have h : Lop b a = ell b (Finsupp.single [] (op a)) := by simp
  rw [h]; exact ell_mem b hone _

theorem Pw_mem (w : List X) : Pw B w ∈ PRing b hone := by
  rw [← ell_single_one b w]; exact ell_mem b hone _

theorem J_mem (m : M) : J b m ∈ PRing b hone := ell_mem b hone _

theorem PRing_ext {f f' : PRing b hone}
    (h : (f : Op B X) (Finsupp.single [] 1) = (f' : Op B X) (Finsupp.single [] 1)) : f = f' := by
  apply Subtype.ext
  rw [← (mem_PRing b hone).1 f.2, ← (mem_PRing b hone).1 f'.2, h]

noncomputable def iota : B →+* PRing b hone :=
  (LopHom b hone).codRestrict (PRing b hone) (Lop_mem b hone)

@[simp]
theorem coe_iota (a : B) : (iota b hone a : Op B X) = Lop b a := rfl

noncomputable def word (w : List X) : PRing b hone := ⟨Pw B w, Pw_mem b hone w⟩

@[simp]
theorem coe_word (w : List X) : (word b hone w : Op B X) = Pw B w := rfl

noncomputable def coeff : PRing b hone →+ (List X →₀ B) where
  toFun f := Finsupp.mapRange unop unop_zero ((f : Op B X) (Finsupp.single [] 1))
  map_zero' := by simp
  map_add' f f' := by
    ext w
    simp

@[simp]
theorem coeff_apply (f : PRing b hone) (w : List X) :
    coeff b hone f w = unop ((f : Op B X) (Finsupp.single [] 1) w) := by
  simp [coeff]

theorem coeff_injective : Function.Injective (coeff b hone) := by
  intro f f' h
  apply PRing_ext
  ext w
  have := DFunLike.congr_fun h w
  rw [coeff_apply, coeff_apply] at this
  exact unop_injective this

noncomputable def jHom : M →+ PRing b hone :=
  (J b).codRestrict (PRing b hone) (J_mem b hone)

@[simp]
theorem coe_jHom (m : M) : (jHom b hone m : Op B X) = J b m := rfl

theorem jHom_one : jHom b hone (b none) = 1 :=
  Subtype.ext (by rw [coe_jHom, J_basis]; simp)

theorem jHom_left (c : B) (m : M) : jHom b hone (c • m) = iota b hone c * jHom b hone m :=
  Subtype.ext (J_left b hone c m)

theorem jHom_right (c : B) (m : M) :
    jHom b hone (op c • m) = jHom b hone m * iota b hone c :=
  Subtype.ext (J_smul b hone (op c) m)

end Ring

section WordBasis

variable {B : Type*} [DivisionRing B] {X : Type*} {M : Type*} [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M] (b : Module.Basis (Option X) Bᵐᵒᵖ M)
  (hone : ∀ c : B, c • b none = op c • b none)

noncomputable def wordBasis : WordBasis B X (PRing b hone) where
  ι := iota b hone
  word := word b hone
  coeff := coeff b hone
  word_nil := Subtype.ext Pw_nil
  word_append u v := Subtype.ext (Pw_append u v)
  coeff_injective := coeff_injective b hone
  coeff_ι c := by
    ext w
    simp [Lam_nil, Finsupp.single_apply, apply_ite unop]
  coeff_word_mul u r w := by
    rw [coeff_apply, coeff_apply, Subring.coe_mul, Module.End.mul_apply, coe_word,
      Pw_apply_append]
  coeff_word_mul_of_not_prefix u r w h := by
    rw [coeff_apply, Subring.coe_mul, Module.End.mul_apply, coe_word,
      Pw_apply_of_not_prefix _ _ _ h, unop_zero]
  coeff_mul_ι r c w := by
    have h1 : (Finsupp.single [] (op c) : NF B X) = op c • Finsupp.single [] 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [coeff_apply, coeff_apply, Subring.coe_mul, Module.End.mul_apply, coe_iota,
      Lop_single_one, Lam_nil, h1, map_smul, Finsupp.smul_apply, smul_eq_mul, unop_mul, unop_op]
  filtration c u w h := by
    rw [coeff_apply, Subring.coe_mul, Module.End.mul_apply, coe_iota, coe_word] at h
    have h2 : Pw B u (Finsupp.single [] 1 : NF B X) = Finsupp.single u 1 := by simp
    rw [h2, Lop_single_one] at h
    exact Lam_length_le b u c w (fun h0 => h (by rw [h0, unop_zero]))

end WordBasis

theorem exists_basis_option.{u, v} (K : Type v) [DivisionRing K] {V : Type u} [AddCommGroup V]
    [Module K V] (v : V) (hv : v ≠ 0) :
    ∃ (X : Type u) (b : Module.Basis (Option X) K V), b none = v := by
  classical
  have hli : LinearIndepOn K id ({v} : Set V) := by
    rw [linearIndepOn_singleton_iff]; exact hv
  let i₀ : hli.extend (Set.subset_univ _) := ⟨v, hli.subset_extend _ (Set.mem_singleton v)⟩
  refine ⟨{i // i ≠ i₀}, (Module.Basis.extend hli).reindex (Equiv.optionSubtypeNe i₀).symm, ?_⟩
  simp [i₀]

end FRD.Pointed
