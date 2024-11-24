import BorelDet.Tree.len_tree_hom

namespace GaleStewartGame.Tree
universe u
open CategoryTheory

noncomputable section
/-- A tree with a chosen base node -/
def PointedTrees := Σ (T : Trees), T

/-- a base node preserving morphism of trees -/
@[ext (flat := false)] structure PointedLenHom (S T : PointedTrees)
  extends Tree.LenHom S.1 T.1 where
  hp : toFun S.2 = T.2
variable {S T : PointedTrees} {n : ℕ}
namespace PointedLenHom
def toHom (f : PointedLenHom S T) : S.1 ⟶ T.1 := f.toLenHom
instance : FunLike (PointedLenHom S T) S.1 T.1 where
  coe f := f.toHom
  coe_injective' _ _ h := PointedLenHom.ext <| LenHom.ext h
instance : OrderHomClass (PointedLenHom S T) S.1 T.1 where
  map_rel f _ _ h := f.toOrderHom.monotone' h
@[simp] lemma add_toHom (f : PointedLenHom S T) (x : S.1) :
  f x = f.toHom x := rfl

/-- The category of trees with a chosen base node -/
instance : Category PointedTrees where
  Hom S T := PointedLenHom S T
  id S := ⟨𝟙 S.1, rfl⟩
  comp f g := ⟨f.toHom ≫ g.toHom, by simp; convert g.hp; exact f.hp⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
variable {S T : PointedTrees}
@[ext] lemma ext' {f g : S ⟶ T} (h : f.toLenHom = g.toLenHom) : f = g :=
  PointedLenHom.ext h
@[simp] lemma rem_pointedLenHom : PointedLenHom S T = (S ⟶ T) := rfl
@[simp] lemma rem_toLenHom' (f : S ⟶ T) x :
  DFunLike.coe (F := S.1 ⟶ T.1) f.toLenHom x = f.toHom x := rfl
@[simp] lemma pair_toHom (f : S.1 ⟶ T.1) hf :
  PointedLenHom.toHom ⟨f, hf⟩ = f := rfl
@[simp] lemma hp_simp (f : S ⟶ T) : f.toHom S.2 = T.2 := f.hp
@[simp] theorem id_toLenHom (S : PointedTrees) : (𝟙 S : S ⟶ S).toHom = 𝟙 S.1 := rfl
@[simp] theorem comp_toLenHom {S T U : PointedTrees} (f : S ⟶ T) (g : T ⟶ U) :
  (f ≫ g).toHom = f.toHom ≫ g.toHom := rfl
end PointedLenHom
abbrev forgetPoint : PointedTrees ⥤ Trees where
  obj A := A.1
  map f := f.toHom
instance : forgetPoint.ReflectsIsomorphisms where
  reflects := by
    intro _ _ f _
    use ⟨inv (forgetPoint.map f), by rw [← f.hp]; apply cancel_inv_left (C := Trees)⟩
    constructor <;> (ext x; simp)

@[simp] theorem pointed_isIso_iff {S T : PointedTrees} (f : S ⟶ T) :
  IsIso f ↔ IsIso (forgetPoint.map f) := (isIso_iff_of_reflects_iso f _).symm

section
variable {S T : Trees} {x : List S.1} {a : S.1} (f : S ⟶ T) (hx : x ++ [a] ∈ S.2)
theorem apply_concat :
  ∃ b, (f ⟨_, hx⟩).val = (f ⟨x, mem_of_append hx⟩).val ++ [b] := by
  let ⟨lb, (hlb : (f _).val = (f _).val ++ _)⟩ := apply_append f.toOrderHom hx
  replace hbl := congr_arg List.length hlb
  simp only [LenHom.h_length_simp, List.length_append, List.length_singleton,
    add_right_inj] at hbl
  obtain ⟨b, rfl⟩ := List.length_eq_one.mp hbl.symm; use b
def concat : T.1 := (apply_concat f hx).choose
theorem concat_spec :
  (f ⟨_, hx⟩).val = (f ⟨x, mem_of_append hx⟩).val ++ [concat f hx] :=
  (apply_concat f hx).choose_spec
theorem concat_elem :
  (f ⟨x, mem_of_append hx⟩).val ++ [concat f hx] ∈ T.2 := by
  rw [← concat_spec]; apply SetLike.coe_mem
theorem concat_spec' :
  f ⟨_, hx⟩ = ⟨(f ⟨x, mem_of_append hx⟩).val ++ [concat f hx], concat_elem f hx⟩ := by
  ext1; apply concat_spec
theorem concat_uniq b (hb : (f ⟨x, mem_of_append hx⟩).val ++ [b] = (f ⟨_, hx⟩).val) :
  concat f hx = b := by
  symm; rwa [← List.singleton_inj, ← List.append_right_inj, ← concat_spec]
end

abbrev extensionsPre : Prefunctor PointedTrees (Type u) where
  obj T := { a : T.1.1 | T.2.val ++ [a] ∈ T.1.2 }
  map f a := ⟨concat (forgetPoint.map f) a.prop, by
    dsimp only [Set.mem_setOf_eq]; erw [← f.hp, ← concat_spec]; apply SetLike.coe_mem⟩
def extensions : PointedTrees ⥤ Type u where
  toPrefunctor := extensionsPre
  map_id _ := by
    ext; simp_rw [PointedLenHom.id_toLenHom, types_id_apply]
    apply concat_uniq; simp
  map_comp _ _ := by
    ext; simp_rw [PointedLenHom.comp_toLenHom, types_comp_apply]
    apply concat_uniq; simp_rw [comp_apply, concat_spec']
    congr!; rw [← PointedLenHom.hp]; rfl

def extensions.val' {T : PointedTrees} (a : extensions.obj T) : List T.1.1 :=
  T.2.val ++ [a.val]
@[simps] def extensions.valT' {T : PointedTrees} (a : extensions.obj T) : T.1 :=
  ⟨extensions.val' a, a.prop⟩
@[simp] theorem extensions_map_val' {S T : PointedTrees}
  (f : S ⟶ T) (a : extensions.obj S) :
  extensions.val' (extensions.map f a) = (f.toHom ⟨extensions.val' a, a.prop⟩).val := by
  simp [extensions.val', extensions, concat_spec']
@[simp] theorem extensions_map_valT' {S T : PointedTrees}
  (f : S ⟶ T) (a : extensions.obj S) :
  extensions.valT' (extensions.map f a) = f.toHom ⟨extensions.val' a, a.prop⟩ :=
  tree_ext (extensions_map_val' f a)
abbrev mkPointed {T : Trees} (x : T) : PointedTrees := ⟨T, x⟩
def mkPointedMor {S T : Trees} (f : S ⟶ T) (x : S) :
  mkPointed x ⟶ mkPointed (f x) := ⟨f, rfl⟩

namespace ExtensionsAt
variable {S T : Trees} (f : S ⟶ T) {x : T}
theorem eq_obj (x : T) : ExtensionsAt x = extensions.obj (mkPointed x) := rfl
abbrev map ⦃x : S⦄ ⦃y : T⦄ (h : f x = y) (a : ExtensionsAt x) : ExtensionsAt y :=
  extensions.map (X := mkPointed x) (Y := mkPointed y) ⟨f, h⟩ a
@[simp] theorem map_val' ⦃x : S⦄ ⦃y : T⦄
  (h : f x = y) (a : ExtensionsAt x) : (map f h a).val' (A := no_index _) = (f a.valT').val :=
  extensions_map_val' (S := mkPointed x) (T := mkPointed y) ⟨f, h⟩ a
@[simp] theorem map_valT' ⦃x : S⦄ ⦃y : T⦄ (h : f x = y) (a : ExtensionsAt x) :
  (map f h a).valT' (A := no_index _) = f a.valT' :=
  extensions_map_valT' (S := mkPointed x) (T := mkPointed y) ⟨f, h⟩ a
end ExtensionsAt

end
end GaleStewartGame.Tree
