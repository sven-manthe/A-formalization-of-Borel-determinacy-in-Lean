import Mathlib.CategoryTheory.Adjunction.Limits
import BorelDet.Tree.restrict_tree
import BorelDet.Basic.inv_limit_nat

namespace GaleStewartGame.Tree
open Classical CategoryTheory

noncomputable section
universe u
variable {A B : Type u} {m k n : ℕ}
/-- Object function of adjoint of `res k` -/
def constTreeObj (k : ℕ) (A : Type u) : Tree A where
  val := {x | ∃ m ≤ k, x ∈ Set.range (List.replicate m)}
  property := by
    rintro x a ⟨m, hm, ⟨b, h⟩⟩; rcases m with _ | m
    · simp at h
    · rw [List.replicate_succ'] at h
      exact ⟨m, ⟨by omega, ⟨b, List.append_inj_left' h rfl⟩⟩⟩
@[simp] theorem mem_constTree (a : A) (h : m ≤ k) :
  List.replicate m a ∈ constTreeObj k A := by
  use m; simp [h]
def headD (x : constTreeObj k A) : A := x.prop.choose_spec.2.choose
@[simp] theorem eq_replicate_headD (x : constTreeObj k A) :
  List.replicate x.val.length (headD x) = x := by
  nth_rw 2 [← x.prop.choose_spec.2.choose_spec]
  nth_rw 1 [← x.prop.choose_spec.2.choose_spec]
  symm; apply List.eq_replicate_of_mem; intro _; apply List.eq_of_mem_replicate
theorem headD_nonempty (x : constTreeObj k A) (h : x.val ≠ []) : headD x = x.val.head h := by
  rw [← eq_replicate_headD] at h; rw [← List.head_replicate h]; simp
@[simp] theorem constTree_length (x : constTreeObj k A) : x.val.length ≤ k := by
  obtain ⟨_, ⟨_, h, ⟨_, rfl⟩⟩⟩ := x; simp [h]
@[simp] theorem constTree_zero (x : constTreeObj 0 A) : x.val = [] := by
  apply List.eq_nil_of_length_eq_zero; linarith [constTree_length x]
/-- Adjoint of `res k` -/
def constTree (k : ℕ) : Type u ⥤ Trees where
  obj A := ⟨A, constTreeObj k A⟩
  map f := {
    toFun := fun ⟨x, h⟩ ↦ ⟨List.map f x, by
      obtain ⟨n, _, ⟨_, rfl⟩⟩ := h; use n; rw [List.map_replicate]; tauto⟩
    monotone' := fun _ _ h ↦ List.IsPrefix.map _ h
    h_length := by simp
  }
  map_id _ := ConcreteCategory.hom_ext _ _ fun x ↦ tree_ext x.val.map_id
  map_comp f g := ConcreteCategory.hom_ext _ _ fun x ↦ tree_ext (List.map_map g f x.val).symm
@[simp] theorem head_constTree_map (k : ℕ) (f : A → B) {x : constTreeObj k A} (h : x.val ≠ []) :
  List.head (((constTree k).map f) x).val (LenHom.map_ne_nil _ h)
  = f (List.head x.val h) := by simp [constTree, ← rem_toFun]
def resEq_unit k : 𝟭 _ ⟶ constTree k ⋙ resEq k where
  app _ a := ⟨List.replicate k a, by simp [constTree]⟩
  naturality _ _ _ := types_ext _ _ fun x ↦ resEq_ext _ _ List.map_replicate.symm
def resEq_counit_comp k T : (constTree k).obj ((resEq k).obj T) ⟶ T where
  toFun := fun x ↦ take x.val.length ⟨(headD x).val, by simp⟩
  monotone' := by
    intro x y h; dsimp only [rem_trees_snd]; by_cases hx : x.val = []
    · simp only [hx, take_coe, List.length_nil, le_def_trees, List.take_zero, List.nil_prefix]
    · have h' : headD x = headD y := by simpa only [← headD_nonempty] using h.head hx
      simp only [h', Functor.comp_obj, le_def_trees, List.prefix_take_iff,
        List.take_prefix, List.length_take, resEq_len, ge_iff_le, constTree_length,
        min_eq_left, List.IsPrefix.length_le h, and_self, take_coe]
  h_length _ := by simp only [take_coe, List.length_take, resEq_len, constTree_length, min_eq_left]
def resEq_counit k : resEq k ⋙ constTree k ⟶ 𝟭 _ where
  app := resEq_counit_comp k
  naturality := by
    rintro _ _ f; ext x
    simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, comp_apply, LenHom.mk_eval,
      LenHom.h_length_simp, Functor.id_map, take_coe, resEq_counit_comp]
    rw [take_apply f x.val.length]
    by_cases hxl : x.val = []
    · rw [congr_arg List.length hxl]; rfl
    · rw [headD_nonempty]; simp_rw [headD_nonempty _ hxl]
      rw [head_constTree_map]; rfl
def resEqAdj (k : ℕ) : constTree k ⊣ resEq k := Adjunction.mkOfUnitCounit {
  unit := resEq_unit k
  counit := resEq_counit k
  left_triangle := by
    ext A x; simp only [Functor.comp_obj, Functor.id_obj, resEq_counit,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, whiskerLeft_app,
      Category.id_comp, comp_apply, LenHom.mk_eval, LenHom.h_length_simp, Set.mem_setOf_eq,
      NatTrans.id_app', id_apply, take_coe, resEq_counit_comp]
    by_cases hxl : x.val = []
    · rw [congr_arg List.length hxl, hxl]; rfl
    · rw [headD_nonempty, head_constTree_map, ← headD_nonempty _ hxl, resEq_unit]
      simp only [List.take_replicate, constTree_length, min_eq_left, eq_replicate_headD]
  right_triangle := by
    ext T (x : (resEq k).obj T); dsimp; ext1
    simp only [Functor.id_obj, resEq_counit, FunctorToTypes.comp, whiskerLeft_app,
      Functor.associator_inv_app, Functor.comp_obj, types_id_apply, whiskerRight_app,
      resEq_map, LenHom.mk_eval, resEq_len, NatTrans.id_app', take_coe, resEq_counit_comp]
    have hxl : x.val.length = k := x.prop.2
    rcases k with _ | _
    · simpa only [List.take_zero] using (List.eq_nil_of_length_eq_zero hxl).symm
    · rw [headD_nonempty _ (fun h ↦ by injection h)]
      simp_rw [resEq_unit, List.head_replicate, ← hxl, List.take_length]
}
instance (k : ℕ) : Functor.IsRightAdjoint (Tree.resEq k) :=
  ⟨Tree.constTree k, ⟨Tree.resEqAdj k⟩⟩
instance (k : ℕ) : Limits.PreservesLimitsOfSize (Tree.resEq k) :=
  (Tree.resEqAdj k).rightAdjoint_preservesLimits

section TreeLimits
variable {J : Type} [Category J] (F : J ⥤ Trees)
/-- Object function of limit functor in `Trees` -/
def limObj : Tree (∀ j, (F.obj j).1) where
  val := { x | ∃ (h : ∀ j, x.mapEval j ∈ (F.obj j).2),
    ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f ⟨_, h i⟩).val = x.mapEval j }
  property := by
    intro x a ⟨h1, h2⟩; use fun j ↦ mem_of_append (y := [a j]) (by
      simpa only [List.map_append, List.map_cons, List.map_nil] using h1 j)
    intro _ _ f; specialize h2 f; apply_fun List.take x.length at h2
    simp_rw [List.map_append, List.map_cons, List.map_nil, ← take_apply_val] at h2
    convert h2 <;> simp only [List.length_map, le_refl, List.take_append_of_le_length,
      ← List.map_take, List.take_length, take_coe]
def limCone : Limits.Cone F where
  pt := ⟨_, limObj F⟩
  π := {
    app := fun j ↦ {
      toFun := fun x ↦ ⟨x.val.mapEval j, x.prop.1 j⟩
      monotone' := fun _ _ h ↦ h.map _
      h_length := by simp_rw [List.length_map, implies_true]
    }
    naturality := fun _ _ f ↦ ConcreteCategory.hom_ext _ _ fun x ↦ tree_ext (x.prop.2 f).symm
  }
def isLimit_lift (s : Limits.Cone F) : s.pt ⟶ (limCone F).pt where
  toFun x := ⟨List.zipFun (n := x.val.length) (fun j ↦ ((s.π.app j) x).val)
    (fun _ ↦ LenHom.h_length_simp _ x), by
    simp only [limCone, limObj, OrderHom.toFun_eq_coe, rem_toOrderHom,
      Functor.const_obj_obj, Set.mem_setOf_eq, List.mapEval_zip, Subtype.coe_eta,
      SetLike.coe_mem, implies_true, exists_const]
    intro _ _ f; rw [← s.w f]; rfl⟩
  monotone' x y h := List.zipFun_mono _ _ _ _ h.length_le (fun j ↦ (s.π.app j).monotone' h)
  h_length _ := by simp only [List.zipFun_len]

def isLimit : Limits.IsLimit (limCone F) where
  lift := isLimit_lift F
  fac := by
    intros; ext
    simp_rw [isLimit_lift, comp_apply, limCone, Functor.const_obj_obj,
      LenHom.mk_eval, List.mapEval_zip]
  uniq := by
    intro s f h; ext1; ext1
    simp_rw [isLimit_lift, LenHom.mk_eval]
    apply List.mapEval_joint_epi <;>
      simp only [LenHom.h_length_simp, List.zipFun_len, List.mapEval_zip]
    simp_rw [← h]; intro _; rfl
end TreeLimits

theorem proj_fixing (F : ℕᵒᵖ ⥤ Trees) (k : ℕ)
  (hF : ∀ n, Tree.Fixing (k + n) (F.map (homOfLE (Nat.le_succ n)).op)) n :
  Fixing (k + n) ((limCone F).π.app (Opposite.op n)) :=
  (fixing_iff_fixingEq (k + n) _).mpr (fun m hm ↦
    ⟨nat_add_initial (Limits.isLimitOfPreserves (resEq m) (isLimit F)) n (fun p hp ↦
      ((fixing_iff_fixingEq (k + n) _).mp (by synth_fixing) m hm).prop) n le_rfl⟩)

end
end GaleStewartGame.Tree
