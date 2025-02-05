import Mathlib.SetTheory.Descriptive.Tree
import BorelDet.Basic.fin_lists

namespace GaleStewartGame
open Descriptive
@[simps!] instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet
namespace Tree
variable {A A' : Type*} (S T : tree A) (x y : List A)
section
attribute [local instance] SetLike.instSubtypeSet
variable {X} {p : Set X → Prop} {x : X} {U : Set X} {h : p U}
universe u in
@[simp] lemma mem_mk' : x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl
end

lemma take_mem {T : tree A} {n : ℕ} (x : T) : x.val.take n ∈ T :=
  mem_of_prefix (x.val.take_prefix n) x.prop
/-- A variant of `List.take` internally to a tree -/
@[simps coe] def take {T : tree A} (n : ℕ) (x : T) : T := ⟨x.val.take n, take_mem x⟩
@[simp] lemma take_take {T : tree A} (m n : ℕ) (x : T) :
  take m (take n x) = take (m ⊓ n) x := by simp [Subtype.ext_iff, List.take_take]
@[simp] lemma take_eq_take {x : T} {m n : ℕ} :
  take m x = take n x ↔ m ⊓ x.val.length = n ⊓ x.val.length := by simp [Subtype.ext_iff]

lemma singleton_mem (T : tree A) {a : A} {x : List A} (h : a :: x ∈ T) : [a] ∈ T :=
  mem_of_prefix ⟨x, rfl⟩ h
instance : Trans (List.IsPrefix) (fun x (T : tree A) ↦ x ∈ T) (fun x (T : tree A) ↦ x ∈ T)
  where trans := mem_of_prefix

/-- The residual tree obtained by regarding the node x as new root -/
def subAt : tree A := ⟨(x ++ ·)⁻¹' T, fun _ _ _ ↦ mem_of_append (by rwa [List.append_assoc])⟩
@[simp] lemma subAt_nil : subAt T [] = T := rfl
@[simp] lemma subAt_append : subAt (subAt T x) y = subAt T (x ++ y) := by simp [subAt]
@[gcongr] lemma subAt_mono {S T : tree A} (h : S ≤ T) :
  subAt S x ≤ subAt T x := Set.preimage_mono h
@[simp] lemma mem_subAt : y ∈ subAt T x ↔ x ++ y ∈ T := Iff.rfl
@[simps coe] def drop {T : tree A} (n : ℕ) (x : T) : subAt T (Tree.take n x).val :=
  ⟨x.val.drop n, by simp⟩

/-- Adjoint of `subAt` -/
def pullSub : tree A where
  val := { y | y.take x.length <+: x ∧ y.drop x.length ∈ T }
  property := fun y a ⟨h1, h2⟩ ↦
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩
lemma mem_pullSub_short {x y : List A} {T : tree A} (hl : y.length ≤ x.length) :
  y ∈ pullSub T x ↔ y <+: x ∧ [] ∈ T := by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]
lemma mem_pullSub_long {x y : List A} {T : tree A} (hl : x.length ≤ y.length) :
  y ∈ pullSub T x ↔ ∃ z ∈ T, y = x ++ z := by
  constructor
  · intro ⟨h1, h2⟩; use y.drop x.length, h2; nth_rw 1 [← List.take_append_drop x.length y]
    simpa [- List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  · rintro ⟨_, h, rfl⟩; simp [pullSub, h]
@[simp] lemma mem_pullSub_append {T : tree A} (x y : List A) :
  x ++ y ∈ pullSub T x ↔ y ∈ T := by rw [mem_pullSub_long] <;> simp
@[simp] lemma mem_pullSub_self {T : tree A} (x : List A) :
  x ∈ pullSub T x ↔ [] ∈ T := by simpa using mem_pullSub_append x []
lemma pullSub_subAt (T : tree A) (x : List A) : pullSub (subAt T x) x ≤ T := by
  intro y (h : y ∈ pullSub _ x); rcases le_or_gt y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; simp at h; exact mem_of_prefix h.1 h.2
  · rw [mem_pullSub_long h'.le] at h; obtain ⟨_, h, rfl⟩ := h; exact h
@[simp] lemma subAt_pullSub (T : tree A) (x : List A) : subAt (pullSub T x) x = T := by
  ext y; simp
@[gcongr] lemma pullSub_mono {S T : tree A} (h : S ≤ T) x : pullSub S x ≤ pullSub T x :=
  fun _ ⟨h1, h2⟩ ↦ ⟨h1, h h2⟩
lemma pullSub_adjunction (S T : tree A) (x : List A) : pullSub S x ≤ T ↔ S ≤ subAt T x := by
  constructor <;> intro h
  · rw [← subAt_pullSub S x]; gcongr
  · exact le_trans (by gcongr) (pullSub_subAt T x)
@[simp] lemma pullSub_nil (S : tree A) : pullSub S [] = S := by
  simp [pullSub]
@[simp] lemma pullSub_append (S : tree A) (x y : List A) :
  pullSub (pullSub S y) x = pullSub S (x ++ y) := by
  ext z; rcases le_or_gt x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp; simp_rw [mem_pullSub_append]
      simp [pullSub, List.take_add, List.prefix_append_right_inj]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
        cases hp <| List.prefix_iff_eq_take.mpr (List.IsPrefix.eq_of_length h (by simpa)).symm
  · rw [mem_pullSub_short (by omega), mem_pullSub_short (by simp),
      mem_pullSub_short (by simp; omega)]
    simpa using fun _ ↦ (z.isPrefix_append_of_length hl.le).symm

/-- Set of children of node x as elements of T -/
def ExtensionsAt {T : tree A} (x : T) := { a : A // x.val ++ [a] ∈ T }
namespace ExtensionsAt
variable {S T}
variable {n : ℕ} {x : T} (a : ExtensionsAt x)
/-- The underlying list of a child -/
def val' := x.val ++ [a.val]
@[simps coe] def valT' : T := ⟨a.val', a.prop⟩
@[ext] lemma ext {a b : ExtensionsAt x} (h : a.val = b.val) : a = b := Subtype.ext h
lemma ext_val' {a b : ExtensionsAt x} (h : a.val' = b.val') : a = b := by
  ext; simpa [val'] using h
lemma ext_valT' {a b : ExtensionsAt x} (h : a.valT' = b.valT') : a = b :=
  ext_val' <| congr_arg Subtype.val h
@[simps] def drop {T : tree A} {n : ℕ} {x : T} :
  ExtensionsAt x ≃ ExtensionsAt (Tree.drop n x) where
  toFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  invFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] lemma val'_length :
  a.val' (A := no_index _).length (α := no_index _) = x.val.length (α := no_index _) + 1 := by
  simp [ExtensionsAt.val']
lemma val'_get_last_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'[n]'(by simp [h]) = a.val := by simp [val', h]
@[simp↓ 1100] lemma val'_get_last (a : ExtensionsAt x) :
  a.val' (A := no_index _)[x.val.length (α := no_index _)] = a.val := by simp [val']
lemma val'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  a.val'.take n = x.val.take n := by simpa [val']
lemma val'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'.take n = x.val := by simp [val', h]
@[simp↓ 1100] lemma val'_take (a : ExtensionsAt x) :
  a.val' (A := no_index _).take (x.val.length (α := no_index _)) = x.val := by simp [val']
lemma valT'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  take n a.valT' = take n x := Subtype.ext <| a.val'_take_of_le h
lemma valT'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  take n a.valT' = x := Subtype.ext <| a.val'_take_of_eq h
@[simp↓ 1100] lemma valT'_take (a : ExtensionsAt x) :
  take (x.val.length (α := no_index _)) a.valT'  (A := no_index _) = x := Subtype.ext a.val'_take
end ExtensionsAt

/-- A tree is pruned if it has no leaves -/
def IsPruned : Prop := ∀ x : T, Nonempty (ExtensionsAt x)
lemma IsPruned.sub {T : tree A} (h : IsPruned T) (x : List A) : IsPruned (subAt T x) := by
  intro ⟨y, h'⟩
  simpa only [ExtensionsAt, nonempty_subtype, List.append_assoc, mem_subAt] using h ⟨_, h'⟩
lemma IsPruned.pullSub {T : tree A} (hP : IsPruned T) (x : List A) : IsPruned (pullSub T x) := by
  intro ⟨y, hy⟩; rcases lt_or_ge y.length x.length with h | h
  · rw [mem_pullSub_short (by omega), List.prefix_iff_eq_take] at hy; use x.get ⟨y.length, h⟩
    simp_rw (config := {singlePass := true}) [hy.1]
    simp [h.le, (by omega : y.length + 1 ≤ x.length), List.take_concat_get']
    constructor
    · rw [List.take_take]; apply List.take_prefix
    · rw [List.drop_take]; simpa [h] using hy.2
  · rw [mem_pullSub_long h] at hy; obtain ⟨z, hz, rfl⟩ := hy; obtain ⟨a, ha⟩ := hP ⟨z, hz⟩
    use a; simpa
@[simp] lemma pullSub_ne {T : tree A} x : [] ∈ pullSub T x ↔ [] ∈ T := by
  simp [mem_pullSub_short]
@[simp] lemma top_isPruned [h : Nonempty A]: IsPruned (⊤ : tree A) :=
  fun _ ↦ ⟨h.some, CompleteSublattice.mem_top⟩

/-- Order elements of a tree by the prefix relation -/
@[simps] instance (T : tree A) : PartialOrder T where
  le x y := x.val <+: y.val
  le_refl _ := List.prefix_refl _
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h h' :=
    Subtype.ext <| List.IsPrefix.eq_of_length h <| h.length_le.antisymm h'.length_le
lemma apply_append {S : tree A} {T : tree A'} (f : OrderHom S T)
  {x y : List A} (h : x ++ y ∈ S) :
  ∃ z, (f ⟨x ++ y, h⟩).val = f ⟨x, mem_of_append h⟩ ++ z :=
  let ⟨z, h⟩ := f.monotone (a := ⟨x, mem_of_append h⟩) (b := ⟨_, h⟩) ⟨y, rfl⟩
  ⟨z, h.symm⟩

attribute [simp_lengths] take_coe drop_coe ExtensionsAt.valT'_coe ExtensionsAt.val'_length
end Tree
end GaleStewartGame
