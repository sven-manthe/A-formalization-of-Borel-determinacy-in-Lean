import Mathlib.Order.Category.PartOrd
import Mathlib.Topology.Category.TopCat.Basic
import BorelDet.Tree.trees
import BorelDet.Basic.misc_cat

open CategoryTheory

namespace GaleStewartGame.Tree
open Descriptive
noncomputable section

/-- The objects of the category of trees -/
def Trees := Σ A, tree A
variable {S T U : Trees}
/-- The morphisms in the category of trees, length-preserving order-preserving maps -/
@[ext] structure LenHom (S T : Trees) extends OrderHom S.2 T.2 where
  h_length : ∀ x : S.2, (toFun x).val.length = x.val.length

/-- The category of trees has as objects trees in some set of nodes and as morphisms
  length-preserving order-preserving maps. It is a topos (although this fact is not
  proved here). Namely, the map to Presheaves on ℕ such that evaluation becomes resEq
  and the transition maps are given by `List.take` induces an equivalence -/
instance : Category Trees where
  Hom := LenHom
  id S := ⟨OrderHom.id, fun _ ↦ rfl⟩
  comp f g := ⟨g.toOrderHom.comp f.toOrderHom, fun h ↦ by erw [g.h_length, f.h_length]⟩
def forget_PO : Trees ⥤ PartOrd where
  obj T := { α := T.2 }
  map f := f.toOrderHom
instance : forget_PO.Faithful where
  map_injective {_ _} _ _ h := LenHom.ext (congr_arg OrderHom.toFun h)
instance : HasForget Trees where
  forget := Functor.comp Tree.forget_PO (forget PartOrd)
instance : OrderHomClass (S ⟶ T) S.2 T.2 where
  map_rel f _ _ h := f.toOrderHom.monotone' h

@[simp] lemma rem_lenHom : LenHom S T = (S ⟶ T) := rfl
@[simp] lemma rem_trees_snd : (S.2 : Type _) = S := rfl
@[ext] lemma tree_ext {x y : S} (h : x.val = y.val) : x = y := Subtype.ext h
instance : PartialOrder S := by rw [← rem_trees_snd]; infer_instance
@[simp] lemma le_def_trees (x y : T) : x ≤ y ↔ x.val <+: y.val := Iff.rfl
@[simp] lemma rem_toOrderHom (f : S ⟶ T) :
  DFunLike.coe (F := S →o T) f.toOrderHom = f := rfl
lemma rem_toFun (f : S ⟶ T) (x : S) : f.toFun x = f x := by dsimp
@[simp] lemma forget_map (f : S ⟶ T) : (forget Trees).map f = f := rfl

namespace LenHom
lemma id_toFun (S : Trees) : (𝟙 S : S ⟶ S).toFun = _root_.id := rfl
lemma comp_toFun (f : S ⟶ T) (g : T ⟶ U) :
  (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl
instance {S T : Trees} (f : S ⟶ T) [IsIso f] : IsIso (C := Type*) f.toFun :=
  inferInstanceAs (IsIso ((forget Trees).map f))
lemma inv_toFun {S T : Trees} (f : S ⟶ T) [IsIso f] :
  (inv f).toFun = inv (C := Type*) f.toFun :=
  (IsIso.Iso.inv_hom ((forget Trees).mapIso (asIso f))).symm

@[simp, simp_lengths] lemma h_length_simp (f : S ⟶ T) (x : S) :
  (f x).val.length (α := no_index _) = x.val.length (α := no_index _) := f.h_length x
@[simp] lemma h_length_inv (f : S ⟶ T) [IsIso (C := Type*) (f.toFun)] (x : T) :
  (inv (C := Type _) f.toFun x).val.length = x.val.length := by
  simp [← h_length_simp f]
@[simp] lemma map_nil (f : S ⟶ T) (h : [] ∈ S.2) : (f ⟨[], h⟩).val = [] := by
  apply List.eq_nil_of_length_eq_zero; simp
lemma map_ne_nil (f : S ⟶ T) {x : S} (h : x.val ≠ []) : (f x).val ≠ [] := by
  intro h'; apply_fun List.length at h'
  exact h <| List.length_eq_zero.mp <| by simpa using h'

lemma mk_eval (S T : Trees) (f : S → T) hf1 hf2 (x : S) :
  DFunLike.coe (F := S ⟶ T) (no_index ⟨⟨f, hf1⟩, hf2⟩) x = f x := rfl
end LenHom

lemma take_apply (f : S ⟶ T) (n : ℕ) (x : S) :
  f (take n x) = take n (f x) := by
  ext1; apply List.IsPrefix.eq_of_length
  · simpa [List.prefix_take_iff] using f.monotone' (List.take_prefix n x.val)
  · simp only [LenHom.h_length_simp, take_coe, List.length_take]
lemma take_apply_val (f : S ⟶ T) (n : ℕ) (x : S) :
  (f (take n x)).val = (f x).val.take n :=
  congr_arg Subtype.val (take_apply f n x)
lemma prefix_iff (f : S ⟶ T) x y (hf : Function.Injective f) :
  f x ≤ f y ↔ x ≤ y := by
  constructor <;> intro h
  · simp [List.prefix_iff_eq_take, ← take_apply_val, Subtype.val_inj] at h
    exact List.prefix_iff_eq_take.mpr <| congr_arg Subtype.val (hf h)
  · exact f.monotone' h

instance : (forget Trees).ReflectsIsomorphisms where
  reflects := by
    intro S T f _; constructor
    have : IsIso (C := Type _) f.toFun := by show IsIso ((forget Trees).map f); infer_instance
    use {
      toFun := inv (C := Type _) f.toFun
      monotone' := by
        intro _ _ h
        simp [← (prefix_iff f _ _ ((isIso_iff_bijective _).mp inferInstance).1), h]
      h_length := LenHom.h_length_inv _
    }
    constructor <;> ext1 x <;> [apply cancel_inv_left_types; apply cancel_inv_right_types]

end

end GaleStewartGame.Tree
