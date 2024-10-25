import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Order.CompleteSublattice
import BorelDet.Basic.meta

attribute [simp_lengths] sup_eq_max inf_eq_min
  List.length_append List.length_cons List.length_nil
  List.length_take List.length_drop List.length_map List.length_tail

variable {α β I : Type*} {γ : Type* → Type*} {a : α}
universe u

--used in gale stewart and undetermined
@[simp] theorem Nat.add_div' (k m n : ℕ) (h : n < k) : (k * m + n) / k = m := by
  apply Nat.div_eq_of_lt_le <;> linarith --omega instead of linarith fails for either subgoal
@[simp] theorem Nat.add_sub_sub_of_le {m n p : ℕ} (mn : m ≤ n) (np : n ≤ p) :
  (n - m) + (p - n) = p - m := by
  zify[mn, np, mn.trans np]; simp
@[simp] lemma div_add_self (n : ℕ) : (n + n) % 2 = 0 := by omega
lemma Nat.even_min (m n : ℕ) (hm : Even m) (hn : Even n) : Even (min m n) := by
  by_cases m ≤ n <;> simpa (disch := omega)

@[simp] lemma SetLike.setOf_mem_eq {α β : Type*} [SetLike α β] (a : α) : {b | b ∈ a} = a := rfl
@[simp] theorem Subtype.preimage_image_coe (s : Set α) (t : Set s) :
  ((↑) : s → α) ⁻¹' (((↑) : s → α) '' t) = t := Set.preimage_image_eq t val_injective
lemma Set.hEq_of_image_eq {α} {A A' : Set α} (h : A = A') {B : Set A} {B' : Set A'}
  (h' : Subtype.val '' B = Subtype.val '' B') : HEq B B' := by
  subst h; rw [← Subtype.preimage_image_coe A B, ← Subtype.preimage_image_coe A B', h']
lemma Set.compl_diff (a b : Set α) : (a \ b)ᶜ = b ∪ aᶜ := by
  ext; simp [himp]; tauto
--cf. exists_exists_eq_and
theorem exists_exists_and_eq {f : α → β} {p : β → Prop} :
    (∃ b, p b ∧ (∃ a, b = f a)) ↔ ∃ a, p (f a) := by aesop
theorem exists_exists_and_eq' {f : α → β} {p : β → Prop} {r : α → Prop} :
    (∃ b, p b ∧ (∃ a, r a ∧ b = f a)) ↔ ∃ a, r a ∧ p (f a) := by aesop
@[simp] lemma imp_forall_iff_forall (A : Prop) (B : A → Prop) :
  (A → ∀ h : A, B h) ↔ ∀ h : A, B h := by tauto
lemma Disjoint.subset_iff_empty {s t : Set α} (h : Disjoint s t) : s ⊆ t ↔ s ⊆ ∅ := by
  rw [Set.disjoint_iff_inter_eq_empty] at h
  constructor <;> intro h' x hx
  · exact h.subset ⟨hx, h' hx⟩
  · cases h' hx
lemma pairwiseDisjoint_iff {α: I → Type*} (f : ∀ i, α i → β) :
  Set.univ.PairwiseDisjoint (fun i ↦ Set.range (f i)) ↔ ∀ ⦃i x j y⦄, f i x = f j y → i = j := by
  constructor
  · intros h i x j y he; by_contra hne
    apply @h i trivial j trivial hne {f i x}
    · rintro _ rfl; use x
    · rintro _ rfl; use y; exact he.symm
    · rfl
  · intros h i _ j _ ij _ hi hj _ hx; obtain ⟨_, rfl⟩ := hi hx; obtain ⟨_, he⟩ := hj hx
    exact ij <| h he.symm

lemma sigma_eq {β: α → Sort*} {a a' : α} (h : a = a') {b : β a} :
  PSigma.mk a b = PSigma.mk a' (cast (by rw [h]) b : β a') := by
  subst h; rfl

namespace CompleteSublattice
noncomputable def incl {L' : Type*} [CompleteLattice L']
  (L : CompleteSublattice L') : CompleteLatticeHom L L' where
  toFun := Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl
variable {X : Type*} {L : CompleteSublattice (Set X)}
  {S T : L} {s : Set L} {I : Sort*} {f : I → L} {x : X}
@[simps coe] instance : SetLike L X where
  coe T := T
  coe_injective' _ := by simp
@[simp] theorem apply_carrier : x ∈ L.incl T ↔ x ∈ T := Iff.rfl
@[simp] theorem mem_sInf :
  x ∈ sInf s ↔ ∀ T ∈ s, x ∈ T := by rw [← apply_carrier]; simp
@[simp] theorem mem_iInf :
  x ∈ ⨅ (i : I), f i ↔ ∀ (i : I), x ∈ f i := by rw [← apply_carrier]; simp
@[simp] theorem mem_inf :
  x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by rw [← apply_carrier]; simp
@[simp] theorem mem_top : x ∈ (⊤ : L) := by rw [← apply_carrier]; simp
@[simp] theorem mem_sSup :
  x ∈ sSup s ↔ ∃ T ∈ s, x ∈ T := by rw [← apply_carrier]; simp
@[simp] theorem mem_iSup :
  x ∈ ⨆ (i : I), f i ↔ ∃ (i : I), x ∈ f i := by rw [← apply_carrier]; simp
@[simp] theorem mem_sup :
  x ∈ S ⊔ T ↔ x ∈ S ∨ x ∈ T := by rw [← apply_carrier]; simp
@[simp] theorem mem_bot : ¬ x ∈ (⊥ : L) := by rw [← apply_carrier]; simp
@[simp] lemma mem_coe : x ∈ T.val ↔ x ∈ T := Iff.rfl
@[simp] lemma mem_mk U h : x ∈ (⟨U, h⟩ : L) ↔ x ∈ U := Iff.rfl
@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.coe_injective <| Set.ext h
end CompleteSublattice

noncomputable def uncurryProp {α : Type*} {β : α → Prop} {γ : ∀ a, β a → Sort*} --exists already?
  (f : ∀ (x) (y : β x), γ x y) (x : {a | β a}) : γ x.val x.prop := f x.val x.prop

open Cardinal
theorem equals_nonempty_some {A : Set α} {ne : A.Nonempty} (h : a = ne.some) : a ∈ A := --avoid
  cast (h.symm ▸ refl (Set.Nonempty.some _ ∈ _)) (Set.Nonempty.some_mem ne)
theorem Cardinal.choose_injection {α β : Type u} (f : α → Set β) (h : ∀ a, #α ≤ #(f a)) :
  ∃ g : α→β, Function.Injective g ∧ ∀ a, g a ∈ f a := by
  have ⟨wo, hwo, hwol⟩ := Cardinal.ord_eq α
  let recg (a : α) (recg : (b : α) → wo b a → β) : β := by
    let exclude := Set.range (uncurryProp recg)
    have exclsmall : #exclude ≤ (Ordinal.typein wo a).card :=
      Cardinal.mk_le_of_surjective Set.surjective_onto_range
    have h' := lt_of_lt_of_le (lt_of_le_of_lt exclsmall (Cardinal.card_typein_lt wo a hwol)) (h a)
    have h''' : Set.Nonempty (f a \ exclude) := by
      apply Set.nonempty_iff_ne_empty.mpr; intro h
      exact not_le_of_lt h' (Cardinal.mk_le_mk_of_subset (Set.diff_eq_empty.mp h))
    exact h'''.some
  use hwo.fix wo recg; constructor --since mathlib update need wo, should be implicit
  · intro a a' he; wlog h : wo a a'
    · by_contra he2
      have h : wo a' a := by have := hwo.trichotomous a a'; tauto
      apply he2; symm; apply this _ _ _ _ _ (Eq.symm he) <;> assumption
    · rw [hwo.fix_eq wo recg a'] at he
      cases (equals_nonempty_some he).2 ⟨⟨a, h⟩, rfl⟩
  · intro a; rw [hwo.fix_eq wo recg]; exact Set.diff_subset (Set.Nonempty.some_mem _)
