import BorelDet.Tree.tree_lim
import BorelDet.Tree.pointed_trees

namespace Descriptive.Tree
open Classical CategoryTheory Descriptive

noncomputable section
variable {k m n : ℕ}
abbrev mkPointedMor' {S T : Trees} (f : S ⟶ T) (y : T)
  (h : Fixing y.val.length f := by all_goals as_aux_lemma => synth_fixing) : --TODO as_aux_lemma fails on zero goals
  mkPointed (Tree.pInv f y) ⟶ mkPointed y := ⟨f, by simp⟩

abbrev pointedResObj (k : ℕ) (T : PointedTrees) : PointedTrees where
  fst := (Tree.res k).obj T.1
  snd := ⟨T.2.val.take k, by simp only [res, id_eq, Set.coe_setOf, Set.mem_setOf_eq, take_mem,
    List.length_take, inf_le_left, and_self]⟩
/-- restriction of a pointed tree, obtained by replacing
  the base node by an ancestor if necessary -/
def pointedRes (k : ℕ) : PointedTrees ⥤ PointedTrees where
  obj := pointedResObj k
  map {S T} f := ⟨(forgetPoint ⋙ res k).map f, by
    ext1; show (f.toHom (Tree.take k S.2)).val = _
    rw [take_apply_val _ k]; simp⟩
  map_id _ := rfl
  map_comp _ _ := PointedLenHom.ext rfl
lemma pointedRes_isIso_iff_fixing k {S T : PointedTrees} (f : S ⟶ T) :
  IsIso ((pointedRes k).map f) ↔ Fixing k f.toHom := by
    simp [pointedRes]; use Fixing.mk, fun h ↦ h.prop
def extensionsRes T :
  extensions.obj T ≃ extensions.obj ((pointedRes (T.2.val.length + 1)).obj T) where
  toFun a := ⟨a.val, by
    constructor
    · dsimp [pointedRes]; rw [List.take_of_length_le (by omega)]; exact a.prop
    · simp only [pointedRes, List.length_append, List.length_take,
        le_add_iff_nonneg_right, zero_le, min_eq_right, List.length_singleton, le_refl]⟩
  invFun a := ⟨a.val, by
    simpa only [pointedRes, List.take_of_length_le (Nat.le_succ T.2.val.length)] using a.prop.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] lemma extensionsRes_val' {T : Trees} {x : T} (a : ExtensionsAt x) :
  extensions.val' (extensionsRes (mkPointed x) a) = a.val' := by
  simp only [extensions.val', ExtensionsAt.val', pointedRes,
    le_add_iff_nonneg_right, zero_le, List.take_of_length_le]; rfl
@[simp] lemma extensionsRes_symm_val' {T : Trees} {x : T} a :
  ExtensionsAt.val' (A := no_index _) ((extensionsRes (mkPointed x)).symm a)
  = extensions.val' a := by
  simp only [extensions.val', ExtensionsAt.val', pointedRes,
    le_add_iff_nonneg_right, zero_le, List.take_of_length_le]; rfl
@[simp] lemma cast_val' {S : PointedTrees} (h : k = m)
  (a : extensions.obj ((pointedRes k).obj S)) :
  extensions.val' (cast (by rw [h]) a : extensions.obj ((pointedRes m).obj S))
  = extensions.val' a := by subst h; rfl

variable {S T : Trees} (f : S ⟶ T) (x : S) (y : T)
/-- if f is (|x|+1)-fixing, then it induces a bijection on extensions of x -/
def pointedRes_iso (hx : Fixing (x.val.length + 1) f := by as_aux_lemma => synth_fixing) :
  (pointedRes (x.val.length + 1)).obj (mkPointed x)
  ≅ (pointedRes (x.val.length + 1)).obj (mkPointed (f x)) :=
  have _: IsIso ((pointedRes (x.val.length + 1)).map (mkPointedMor f x)) :=
    (pointedRes_isIso_iff_fixing _ _).mpr hx
  asIso ((pointedRes (x.val.length + 1)).map (mkPointedMor f x))
def extensionsEquiv (hx : Fixing (x.val.length + 1) f := by as_aux_lemma => synth_fixing) :
  ExtensionsAt x ≃ ExtensionsAt (f x) :=
  (extensionsRes (mkPointed x)).trans (
  (Iso.toEquiv (extensions.mapIso (pointedRes_iso f x))).trans (
  (Equiv.cast (by simp)).trans (
  extensionsRes (mkPointed (f x))).symm))
@[simp] lemma extensionsEquiv_val' (a : ExtensionsAt x) hx :
  (extensionsEquiv f x hx a).valT' = f a.valT' := by
  ext1
  simp only [ExtensionsAt.valT'_coe, ExtensionsAt.eq_obj, extensionsEquiv, Equiv.trans_apply,
    Iso.toEquiv_fun, Functor.mapIso_hom, Equiv.cast_apply, extensionsRes_symm_val',
    LenHom.h_length_simp, cast_val', extensions_map_val', extensionsRes_val']; rfl
@[simp] lemma extensionsEquiv_symm_val'
  (hx : Fixing (x.val.length + 1) f ) (a : ExtensionsAt (f x)) :
  ((extensionsEquiv f x hx).symm a).valT' = pInv f a.valT' := by
  obtain ⟨a, rfl⟩ := (extensionsEquiv f x).surjective a
  simp only [Equiv.symm_apply_apply, extensionsEquiv_val', cancel_pInv_left]
def pointedRes_iso' (hy : Fixing (y.val.length + 1) f := by as_aux_lemma => synth_fixing) :
  (pointedRes (y.val.length + 1)).obj (mkPointed y)
  ≅ (pointedRes (y.val.length + 1)).obj (mkPointed (pInv f y)) :=
  have _: IsIso ((pointedRes (y.val.length + 1)).map (mkPointedMor' f y)) :=
    (pointedRes_isIso_iff_fixing _ _).mpr hy
  (asIso ((pointedRes (y.val.length + 1)).map (mkPointedMor' f y))).symm
def extensionsEquiv' (hy : Fixing (y.val.length + 1) f := by as_aux_lemma => synth_fixing) :
  ExtensionsAt y ≃ ExtensionsAt (pInv f y) :=
  have : Fixing y.val.length f := by synth_fixing
  (extensionsRes (mkPointed y)).trans (
  (Iso.toEquiv (extensions.mapIso (pointedRes_iso' f y hy))).trans (
  (Equiv.cast (by simp)).trans (
  (extensionsRes (mkPointed (pInv f y))).symm)))
@[simp] lemma extensionsEquiv'_symm_val'
  (hy : Fixing (y.val.length + 1) f) (a : ExtensionsAt (pInv f y)) :
  ((extensionsEquiv' f y hy).symm a).valT' = f a.valT' := by
  ext
  simp_rw [ExtensionsAt.valT'_coe, ExtensionsAt.eq_obj, extensionsEquiv', Equiv.symm_trans_apply,
    ← Equiv.cast_symm, Equiv.symm_symm, Equiv.cast_apply, Iso.toEquiv_symm_fun, Functor.mapIso_inv,
    extensionsRes_symm_val', extensions_map_val']
  simp only [h_length_pInv, cast_val', extensionsRes_val']; rfl
@[simp] lemma extensionsEquiv'_val' (a : ExtensionsAt y) (hy : Fixing (y.val.length + 1) f) :
  (extensionsEquiv' f y hy a).valT' = pInv f a.valT' := by
  obtain ⟨a, rfl⟩ := (extensionsEquiv' f y).symm.surjective a
  simp only [Equiv.apply_symm_apply, extensionsEquiv'_symm_val', cancel_pInv_left]

@[simp] lemma val_res_zero (x : (res 0).obj S) : x.val = [] :=
  List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (res_len_le x))
lemma zero_fixing : Fixing 0 f ↔ ([] ∈ S.2 ↔ [] ∈ T.2) := by
  rw [fixing_iff_forget_isIso]; constructor
  · intro h; constructor <;> intro hn
    · rw [← LenHom.map_nil f hn]; apply SetLike.coe_mem
    · obtain ⟨x, _⟩ := surjective_of_epi ((res 0 ⋙ forget Trees).map f) ⟨[], hn, by simp⟩
      rw [← val_res_zero]; exact x.prop.1
  intro ⟨_, h⟩; apply (isIso_iff_bijective _).mpr; constructor
  · intro x y _; dsimp; ext; simp
  · intro y; use ⟨[], h (by rw [← val_res_zero]; exact y.prop.1), by simp⟩
    dsimp; ext1; simp_rw [LenHom.map_nil, val_res_zero y]

lemma lim_isPruned (F : ℕᵒᵖ ⥤ Trees)
  (hF : ∀ n, Tree.Fixing n (F.map (homOfLE (Nat.le_succ n)).op))
  (h : ∀ n, IsPruned (F.obj (Opposite.op n)).2) :
  IsPruned (limCone F).pt.2 := by
  intro x; have hp := proj_fixing F 0 (by simpa) (x.val.length + 1)
  rw [(extensionsEquiv ((limCone F).π.app ⟨x.val.length + 1⟩) _).nonempty_congr]
  apply h
lemma lim_ne (F : ℕᵒᵖ ⥤ Trees) (hF : ∀ n, Tree.Fixing n (F.map (homOfLE (Nat.le_succ n)).op))
  (h : ∀ n, [] ∈ (F.obj (Opposite.op n)).2) : [] ∈ (limCone F).pt.2 :=
  ((zero_fixing _).mp ((proj_fixing F 0 (by simpa) 0).mon (by simp))).mpr (h 0)
end
end Descriptive.Tree
