import BorelDet.Tree.trees

namespace GaleStewartGame.Tree
open CategoryTheory
open InfList

variable {A : Type*} (S T : Tree A)

def body : Set (ℕ → A) := { y | ∀ x, y ∈ basicOpen x → x ∈ T }
@[gcongr] theorem body_mono {S T : Tree A} (h : S ≤ T) : body S ⊆ body T :=
  fun _ h' x y ↦ h (h' x y)
@[simp] theorem take_mem_body {T : Tree A} {x} (h : x ∈ body T) n : x.take n ∈ T := h _ (by simp)
@[simps coe] def body.take {T : Tree A} (n : ℕ) (x : body T) : T := ⟨_, take_mem_body x.2 n⟩
attribute [simp_lengths] body.take_coe
theorem mem_body_of_take m (T : Tree A) (x : ℕ → A) (h : ∀ n ≥ m, x.take n ∈ T) :
  x ∈ body T := by
  intro y hy; rw [basicOpen_iff_restrict] at hy
  simpa [← hy] using Tree.take_mem ⟨_, h (m + y.length) (by omega)⟩ (n := y.length)
def bodyInfHom : sInfHom (Tree A) (Set (ℕ → A)) where
  toFun := Tree.body
  map_sInf' := by
    intro s; ext a; simp only [body, basicOpen, Set.image_univ, Set.mem_range,
      CompleteSublattice.mem_sInf, forall_exists_index, Set.sInf_eq_sInter, Set.sInter_image,
      Set.mem_iInter]
    constructor
    · rintro h T hT x a rfl; exact h x a rfl _ hT
    · rintro h x a rfl T hT; exact h T hT _ _ rfl
@[simp] theorem body_inter {S T : Tree A} : body (S ⊓ T) = body S ∩ body T := by
  show bodyInfHom (S ⊓ T) = bodyInfHom S ∩ bodyInfHom T; simp
@[simp] lemma body_bot : body (⊥ : Tree A) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]; exact fun x h ↦ h [] (by simp)
@[simp] theorem body_isClosed [TopologicalSpace A] [DiscreteTopology A]:
  IsClosed (body T) := by
  simp_rw [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_nhds_iff]
  intro a ha; simp [body] at ha; let ⟨x, ha1, ha2⟩ := ha
  exact ⟨basicOpen x, fun a ah h ↦ ha2 (h _ ah), basicOpen_isOpen x, ha1⟩

@[simp] theorem subAt_body (x : List A) :
  body (subAt T x) = (x ++ · : (ℕ → A) → ℕ → A)⁻¹' (body T) := by
  ext a; constructor
  · intro h y ⟨b, h'⟩
    specialize h (a.take (y.length - x.length)) (extend_sub _ _)
    obtain ⟨n, h''⟩ := le_iff_exists_add.mp (le_tsub_add (a := x.length))
    simp [append_take] at h h'
    rw [← h', add_comm, h'', ← append_take] at h
    exact mem_of_append h
  · intro h _ _; apply h; simpa

@[simps (config := {fullyApplied := false}) coe]
def body.append {T : Tree A} (x : List A) (y : body (subAt T x)) : body T :=
  ⟨x ++ y.val, by simpa using y.prop⟩
@[simp] lemma body_append_nil (y : body T) : body.append (T := no_index _) [] y = y := rfl
theorem body.append_con {T : Tree A} [TopologicalSpace A] [DiscreteTopology A] (x : List A) :
  Continuous (@body.append A T x) :=
  inducing_subtype_val.continuous_iff.mpr <| (InfList.append_con x).comp continuous_subtype_val
@[congr] lemma range_body_append (x y : List A) (h : x = y) :
  Set.range (@body.append _ T x) = Set.range (@body.append _ T y) := by congr!
@[simp] lemma subtype_body_append x :
  Subtype.val '' Set.range (@body.append _ T x) = basicOpen x ∩ body T := by
  ext a; constructor
  · rintro ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩; simpa using a.prop
  · rintro ⟨⟨b, rfl⟩, ha⟩; use ⟨x ++ b, ha⟩, ⟨⟨b, by simpa⟩, rfl⟩
@[simps (config := {fullyApplied := false}) coe]
def body.drop {T : Tree A} (n : ℕ) (x : body T) : body (subAt T (x.val.take n)) :=
  ⟨tail^[n] x, by simp⟩

section
variable {T : Tree A} (X : Set (body T)) (x : List A)
@[simp] lemma subAt_body_image : Subtype.val '' ((body.append x)⁻¹' X)
  = (x ++ · : (ℕ → A) → ℕ → A)⁻¹' (Subtype.val '' X) := by
  ext; simp; tauto
lemma mem_subAt_body y : y ∈ (body.append x)⁻¹' X ↔ x ++ y.val ∈ Subtype.val '' X := by
  simp [body.append, by simpa using y.prop]
end

@[simp] theorem pullSub_body (T : Tree A) (x : List A) :
  body (pullSub T x) = (x ++ · : (ℕ → A) → ℕ → A) '' body T := by
  ext y; constructor
  · intro h; obtain ⟨z, hzT, hzE⟩ :=
      (mem_pullSub_long (y := y.take x.length) (by simp)).mp (h _ (by simp))
    have hzE' := congr_arg List.length hzE; simp at hzE'
    subst hzE'; simp at hzE
    rw [← take_append x.length y, hzE]; simp
    intro z hz; specialize h (x ++ z); rw [← take_append x.length y, hzE] at h
    simpa using h (by rwa [basicOpen_append])
  · rintro ⟨a, haB, rfl⟩; apply mem_body_of_take x.length
    intro n hn; obtain ⟨m, rfl⟩ := le_iff_exists_add.mp hn; rw [← append_take]
    simp [haB]

theorem IsPruned.body_ne_iff_ne {T : Tree A} (h : IsPruned T) :
  (body T).Nonempty ↔ [] ∈ T := by
  constructor
  · intro ⟨a, ha⟩; apply ha; simp
  · intro hne
    let f (n : ℕ) : T := Nat.recOn n ⟨[], hne⟩ (fun _ p ↦ ⟨_, (Classical.choice (h p)).prop⟩)
    let a (n : ℕ) : A := List.getLast (f (n + 1)).val (by simp [f])
    use a; intro x h'; suffices x = (f x.length).val by rw [this]; exact (f x.length).prop
    induction' x using List.reverseRecOn with x b ih
    · dsimp [f]
    · specialize ih (basicOpen_sub _ _ h'); rw [List.length_append, List.length_eq_one.mpr ⟨b, rfl⟩]
      obtain ⟨z, h'⟩ := h'; apply_fun (fun y ↦ y x.length) at h'; simp at h'
      simp_rw [h', a]; congr!; simp
theorem isPruned_iff_basicOpen_ne {T : Tree A} :
  IsPruned T ↔ ∀ x : T, (basicOpen x ∩ body T).Nonempty := by
  constructor
  · intro hP x; obtain ⟨y, h⟩ := (hP.sub x.val).body_ne_iff_ne.mpr (by simp)
    use x.val ++ y; simpa using h
  · intro h x; obtain ⟨y, hx, hT⟩ := h x; use y x.val.length
    rw [basicOpen_iff_restrict] at hx; nth_rw 1 [hx, ← take_succ']; exact hT _ (extend_sub _ y)

end GaleStewartGame.Tree