import Mathlib.Tactic

universe u
namespace X
open Classical CategoryTheory

noncomputable section
def Tree (A : Type*) : Set (Set (List A)) :=
  {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
instance {A} : SetLike (Tree A) (List A) where
  coe T := T.1
  coe_injective' _ := by sorry
def ExtensionsAt {A} {T : Tree A} (x : T) := { a : A // x.val ++ [a] ∈ T }
section
variable {A : Type*} (T : Tree A)
def PreStrategy := ∀ x : T, Set (ExtensionsAt x)
variable {T p}
def PreStrategy.subtree (S : PreStrategy T) : Tree A where
  val := { x | ∀ {y} {a}, a ∈ S y }
  property := sorry
def Strategy {A : Type*} (T : Tree A) := ∀ x : T, ExtensionsAt x
abbrev Strategy.pre (S : Strategy T) : PreStrategy T := fun x ↦ {S x}
end
def PointedTrees := Σ (T : Σ A, Tree A), T.2
variable {S T : PointedTrees}
instance : Category PointedTrees where
  Hom S T := S.1.2 → T.1.2
  id S := id
  comp f g := g.comp f
variable {S T : Σ A, Tree A}
theorem apply_concat {x : List S.1} {a : S.1} (f : S.2 → T.2) (hx : x ++ [a] ∈ S.2) :
  ∃ b : T.1, (f ⟨x ++ [a], hx⟩).val = [b] := by sorry
def concat {x : List S.1} {a : S.1} (f : S.2 → T.2) (hx : x ++ [a] ∈ S.2) : T.1 := (apply_concat f hx).choose
abbrev extensionsPre : Prefunctor PointedTrees (Type u) where
  obj T := { a : T.1.1 | T.2.val ++ [a] ∈ T.1.2 }
  map f a := ⟨concat f a.prop, by sorry⟩
def fromMap {T : Tree ℕ} (f : T → T) (S : Strategy T) : Strategy T := fun x ↦
  extensionsPre.map (X := ⟨⟨_, T⟩, x⟩) (Y := ⟨⟨_, T⟩, x⟩) f (S x)
variable {G : Tree ℕ}
noncomputable def stratMap' (R : Strategy G) : Strategy G :=
  fun x ↦
  if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else if True then (fromMap (id)) R x
  else (fromMap (id)) R x

set_option profiler true
structure TreeLift where
  R : Strategy G
  x : (stratMap' R).pre.subtree (T := G)
