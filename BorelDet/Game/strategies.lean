import BorelDet.Tree.trees
import BorelDet.Game.player

namespace GaleStewartGame
open Tree
variable {A : Type*} (T : Tree A) (p : Player)
def PreStrategy := ∀ x : T, IsPosition x.val p → Set (ExtensionsAt x) --TODO synth arg?
variable {T p}
namespace PreStrategy
@[ext] lemma ext {f g : PreStrategy T p} (h : ∀ x hp, f x hp = g x hp) : f = g :=
  funext fun x ↦ funext (h x)
instance : PartialOrder (PreStrategy T p) where
  le f g := ∀ x hx, f x hx ⊆ g x hx
  le_refl _ _ _ := subset_rfl
  le_trans _ _ _ ab bc _ _ := subset_trans (ab _ _) (bc _ _)
  le_antisymm _ _ ab ba := PreStrategy.ext fun x hp ↦ subset_antisymm (ab x hp) (ba x hp)
variable (S : PreStrategy T p)

def subtree : Tree A where
  val := { x | ∃ (hx : x ∈ T), ∀ {y} {a}, (hpr : y ++ [a] <+: x) → (hpo : IsPosition y p)
    → ⟨a, mem_of_prefix hpr hx⟩ ∈ S ⟨y, mem_of_append (mem_of_prefix hpr hx)⟩ hpo }
  property := fun _ _ ⟨hx, h⟩ ↦
    ⟨mem_of_append hx, fun hpr _ ↦ h (hpr.trans (List.prefix_append _ _)) _⟩
@[simp] theorem subtree_ne : [] ∈ S.subtree ↔ [] ∈ T := by simp [subtree]
@[simp] theorem subtree_sub : S.subtree ≤ T := fun _ ⟨h, _⟩ ↦ h
@[simps] def subtree_incl (x : S.subtree) : T := ⟨x.val, S.subtree_sub x.prop⟩
attribute [simp_lengths] subtree_incl_coe

@[gcongr] theorem subtree_mono {f g : PreStrategy T p} (h : f ≤ g) : f.subtree ≤ g.subtree :=
  fun _ ⟨hx, h'⟩ ↦ ⟨hx, fun {y} {_} hpr hpo ↦ h ⟨y, _⟩ hpo (h' hpr hpo)⟩
theorem subtree_fair (x : S.subtree) {a : A} (hp : IsPosition x.val p.swap) :
  x ++ [a] ∈ S.subtree ↔ x ++ [a] ∈ T := by
  refine ⟨fun h ↦ S.subtree_sub h, fun ha ↦ ⟨ha, fun {y b} hpr hpo ↦ ?_⟩⟩
  obtain ⟨hx, h'⟩ := x.prop; rcases List.prefix_concat_iff.mp hpr with heq | hpr
  · synth_isPosition
  · exact h' hpr hpo
theorem subtree_compatible (x : S.subtree) (hp : IsPosition x.val p) {a}
  (hx : x.val ++ [a] ∈ S.subtree) : ⟨a, hx.1⟩ ∈ S (S.subtree_incl x) hp :=
  hx.2 List.prefix_rfl _
theorem subtree_compatible_iff (x : S.subtree) (hp : IsPosition x.val p) {a} :
  x.val ++ [a] ∈ S.subtree ↔ ∃ hx : x.val ++ [a] ∈ T, ⟨a, hx⟩ ∈ S (S.subtree_incl x) hp := by
  refine ⟨fun h ↦ ⟨h.1, (subtree_compatible S x hp h)⟩, fun h ↦ ⟨h.1, fun {y b} hpr hpo ↦ ?_⟩⟩
  rcases List.prefix_concat_iff.mp hpr with heq | hpr
  · obtain ⟨rfl, heq⟩ := List.append_inj' heq rfl; obtain rfl := by simpa using heq
    exact h.2
  · apply x.prop.2 hpr
lemma subtree_induction {S S' : PreStrategy T p} {x} (h : x ∈ S.subtree)
  (h' : ∀ n (hn : n < x.length), x.take n ∈ S'.subtree → ∀ hp,
    ⟨x[n], by simpa using take_mem ⟨x, subtree_sub _ h⟩⟩ ∈
      S (Tree.take n (S.subtree_incl ⟨x, h⟩)) hp →
    ⟨x[n], by simpa using take_mem ⟨x, subtree_sub _ h⟩⟩ ∈
      S' (Tree.take n (S.subtree_incl ⟨x, h⟩)) hp) : x ∈ S'.subtree := by
  suffices ∀ n ≤ x.length, x.take n ∈ S'.subtree by simpa using this x.length le_rfl
  intro n hn; induction' n with n ih
  · simpa using mem_of_prefix x.nil_prefix h
  · rw [← List.take_concat_get' _ _ hn]; specialize ih (by omega)
    by_cases hp : IsPosition (x.take n) p
    · rw [S'.subtree_compatible_iff ⟨_, ih⟩ hp]
      use by simpa using S.subtree_sub (take_mem ⟨x, h⟩)
      apply h' n hn ih
      apply S.subtree_compatible (Tree.take _ ⟨x, h⟩); simpa using take_mem ⟨x, h⟩
    · rw [S'.subtree_fair ⟨_, ih⟩ (by synth_isPosition)]
      simpa using S.subtree_sub (take_mem ⟨x, h⟩)

def restrictTree (rto : Tree A) (hr : rto ≤ T) :
  PreStrategy rto p := fun x hx a ↦ S ⟨x.val, hr x.prop⟩ hx ⟨a.val, hr a.prop⟩
abbrev restrict (rto : PreStrategy T p.swap) :
  PreStrategy rto.subtree p := S.restrictTree rto.subtree rto.subtree_sub
theorem restrict_sub (rto : Tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree ≤ S.subtree := fun _ ⟨hx, h⟩ ↦ ⟨hr hx, h⟩
theorem restrict_valid (rto : Tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree ≤ rto := by simp
@[simp] theorem restrict_subtree (rto : Tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree = S.subtree ⊓ rto :=
  le_antisymm
    (le_inf (restrict_sub S rto hr) (restrict_valid S rto hr))
    (fun _ h ↦ ⟨h.2, h.1.2⟩)

def residual (x : List A) :
  PreStrategy (subAt T x) (p.residual x) := fun y hy ↦
    {a | ⟨a.val, by simpa [List.append_assoc] using a.prop⟩ ∈
      S ⟨x ++ y.val, y.prop⟩ (by synth_isPosition)}
lemma sub_residual_subtree (x : List A) :
  subAt S.subtree x ≤ (S.residual x).subtree := by
  intro y ⟨hT, h⟩; use hT; intro _ _ hpr _
  replace hpr := (List.prefix_append_right_inj x).mpr hpr; rw [← List.append_assoc] at hpr
  exact h hpr (by synth_isPosition)
@[simp] theorem residual_subtree (x : S.subtree) :
  (S.residual x).subtree = subAt S.subtree x := by
  ext y; constructor
  · intro ⟨h, h'⟩; use h; intro z a hpr hpo; have ⟨_, hx⟩ := x.prop
    rcases List.prefix_or_prefix_of_prefix hpr (List.prefix_append _ _) with h | ⟨y', h⟩
    · exact hx h hpo
    · induction' y' using List.reverseRecOn with y' b
      · simp [hx, ← h]
      · rw [← List.append_assoc] at h; obtain ⟨rfl, rfl⟩ : x ++ y'= z ∧ b = a := by
          have ⟨hz, ha'⟩ := List.append_inj' h rfl; exact ⟨hz, by injection ha'⟩
        apply h'
        · apply (List.prefix_append_right_inj x).mp; rwa [← List.append_assoc]
        · synth_isPosition
  · apply sub_residual_subtree

def IsQuasi (S : PreStrategy T p) := ∀ x hx, (S x hx).Nonempty
end PreStrategy
variable (T p) in
def QuasiStrategy := PSigma (@PreStrategy.IsQuasi A T p)
@[ext] lemma QuasiStrategy.ext {f g : QuasiStrategy T p} (h : f.1 = g.1) : f = g := by
  obtain ⟨f, hf⟩ := f; obtain ⟨g, hg⟩ := g; simp at h; simp_rw [h] --make general lemma?
variable (T p) in
def Strategy := ∀ x : T, IsPosition x.val p → ExtensionsAt x
@[ext] lemma Strategy.ext {f g : Strategy T p} (h : ∀ x hp, f x hp = g x hp) : f = g :=
  funext fun x ↦ funext (h x)

@[congr] lemma PreStrategy.eval_val_congr {U : Tree A}
  (S S' : PreStrategy U p) (h : S = S') (x x' : U) (h' : x = x') hp :
  Subtype.val '' (S x hp) = Subtype.val '' (S' x' (by subst h'; exact hp)) := by congr!
@[congr] lemma Strategy.eval_val_congr {U : Tree A} (S S' : Strategy U p) (h : S = S') (x x' : U)
  (h' : x = x') hp : (S x hp).val = (S' x' (by subst h'; exact hp)).val := by congr!

abbrev Strategy.pre (S : Strategy T p) : PreStrategy T p := fun x hx ↦ {S x hx}
@[simp] theorem Strategy.isQuasi (S : Strategy T p) : S.pre.IsQuasi := by
  simp [PreStrategy.IsQuasi]
abbrev Strategy.quasi (S : Strategy T p) : QuasiStrategy T p := ⟨S.pre, S.isQuasi⟩
noncomputable def PreStrategy.IsQuasi.choose {S : PreStrategy T p} (h : S.IsQuasi) :
  Strategy T p := fun x hp ↦ (h x hp).some
theorem PreStrategy.choose_sub {S : PreStrategy T p} (h : S.IsQuasi) :
  h.choose.pre ≤ S := by
  intro x hp; simpa [IsQuasi.choose] using (h x hp).some_mem

theorem QuasiStrategy.subtree_isPruned
  (S : QuasiStrategy T p) (hT : IsPruned T) : IsPruned S.1.subtree := by
    intro ⟨x, ⟨hx, h⟩⟩; by_cases hp : IsPosition x p
    · use (S.2 ⟨x, hx⟩ hp).some.val; rw [S.1.subtree_compatible_iff]
      exact ⟨_, (S.2 ⟨x, hx⟩ hp).some_mem⟩
    · obtain ⟨a, ha⟩ := hT ⟨_, hx⟩
      exact ⟨a, (S.1.subtree_fair ⟨x, ⟨hx, h⟩⟩ (by synth_isPosition)).mpr ha⟩
theorem PreStrategy.IsQuasi.restrictTree_isQuasi {S : PreStrategy T p} (rto : Tree A)
  (h : S.IsQuasi) (hfair : ∀ (x : rto) (a : A), IsPosition x.val p →
  x ++ [a] ∈ T → x ++ [a] ∈ rto) (hr : rto ≤ T) : (S.restrictTree rto hr).IsQuasi := by
  intro x hp; let ⟨nev, nep⟩ := h ⟨x.val, hr x.prop⟩ hp
  use ⟨nev.val, hfair _ _ (by synth_isPosition) nev.prop⟩, nep
theorem PreStrategy.IsQuasi.restrict_isQuasi {S : PreStrategy T p} (rto : PreStrategy T p.swap)
  (h : S.IsQuasi) : (S.restrict rto).IsQuasi :=
  restrictTree_isQuasi rto.subtree h (by
    intro x a hp hx; rwa [rto.subtree_fair x (by synth_isPosition)])
    rto.subtree_sub
abbrev QuasiStrategy.restrict
  (S : QuasiStrategy T p) (rto : PreStrategy T p.swap) :
  QuasiStrategy rto.subtree p := ⟨_, S.2.restrict_isQuasi rto⟩
@[simps] def QuasiStrategy.residual (S : QuasiStrategy T p) (x : List A) :
  QuasiStrategy (subAt T x) (p.residual x) := ⟨S.1.residual x, by
  intro y hy; have ne := S.2 ⟨x ++ y.val, y.prop⟩ (by synth_isPosition)
  use ⟨ne.choose.val, by simpa using ne.choose.prop⟩, ne.choose_spec⟩

end GaleStewartGame
