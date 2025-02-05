import BorelDet.Tree.tree_extensions
import BorelDet.Tree.body_functor
import BorelDet.Game.strategies

namespace GaleStewartGame.Tree
open Classical CategoryTheory
open Stream'.Discrete Descriptive

noncomputable section
variable {k m n : ℕ} {S T : Trees} {p : Player}
@[ext] structure BodySystemObj (T : Trees) where
  res : ∀ k, (resEq k).obj T
  con : ∀ k, (res k).val <+: (res (k + 1)).val
@[simp] lemma bodySystem_con' (x : BodySystemObj T) :
  (x.res k).val <+: (x.res m).val ↔ k ≤ m := by
  constructor <;> intro h
  · simpa using h.length_le
  · obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h; induction' n with n ih
    · rfl
    · trans
      · apply ih; omega
      · apply x.con
@[simp] lemma bodySystem_take_val (x : BodySystemObj T) :
  (x.res k).val.take m = (x.res (k ⊓ m)).val := by
  rw [List.prefix_iff_eq_take.mp ((bodySystem_con' x).mpr (by simp : k ⊓ m ≤ k))]
  simp only [resEq_len, List.take_eq_take, inf_le_left, min_eq_left, inf_comm]
@[simp] lemma bodySystem_take (x : BodySystemObj T) :
  Tree.take m (resEq.val' (x.res k)) = resEq.val' (x.res (k ⊓ m)) := by
  ext; simp_rw [take_coe, resEq.val'_coe, bodySystem_take_val]
lemma bodySystem_take' (x : BodySystemObj T) (h : m ≤ k) :
  (x.res k).val.take m = (x.res m).val := by
  simp; congr! <;> simp only [h, inf_of_le_right]
/-- an isomorph of `bodyFunctor` that is more convenient to build levelwise -/
@[simps obj] def bodySystem : Trees ⥤ Type* where
  obj := BodySystemObj
  map f := fun x ↦ {
    res := fun k ↦ (resEq k).map f (x.res k)
    con := by intro _; simp_rw [resEq_map]; apply f.monotone; apply x.con
  }
  map_id _ := rfl
  map_comp _ _ := rfl
@[simps] def bodyEquivSystem_app (T : Trees) : body T.2 ≃ BodySystemObj T where
  toFun x := {
    res := fun k ↦ ⟨x.val.take k, by simp⟩
    con := by simp
  }
  invFun x := ⟨fun n ↦ (x.res (n + 1)).val.get ⟨n, by simp⟩, by
    intro y h; suffices y = (x.res y.length).val by simp only [this, resEq_mem]
    apply List.ext_getElem (by simp); intro n hn; simp only [resEq_len, max_self] at hn
    rw [principalOpen_index] at h
    simp [hn]; rw [← h _ hn]
    apply List.IsPrefix.getElem; rw [bodySystem_con']; omega⟩
  left_inv x := by ext n; simp [Stream'.get]
  right_inv x := by
    ext1; ext1 n; ext1; apply List.ext_getElem (by simp); intro m hm
    simp [Stream'.get] at *
    intro _; apply List.IsPrefix.getElem
    rw [bodySystem_con']; omega
@[simps!] def bodyEquivSystem : bodyFunctor ≅ bodySystem := NatIso.ofComponents
  (fun T ↦ (bodyEquivSystem_app T).toIso) (by
    intro S T f; ext x; dsimp [bodyEquivSystem_app, bodySystem]; ext1; ext1 n; ext1
    apply List.ext_getElem (by simp); intro m hm _
    simp at hm; simp only [bodyMap_restrict]; rfl)

namespace BodySystemObj
abbrev contains (x : BodySystemObj T) (y : List T.1) :=
  y = (x.res y.length).val
abbrev containsTree (x : BodySystemObj T) (y : T) :=
  y = resEq.val' (x.res y.val.length)
lemma bodySystem_contains_iff (x : BodySystemObj T) y :
  x.contains y.val ↔ x.containsTree y := by
  constructor
  · intro h; ext1; exact h
  · apply congr_arg
lemma bodySystem_contains_iff' (x : BodySystemObj T) {z} (y : ExtensionsAt z) :
  x.contains y.val' ↔ x.containsTree y.valT' := bodySystem_contains_iff x y.valT'

@[congr] --simp needs this
lemma res_val_congr (x y : Tree.BodySystemObj T) (h : x = y)
  (h' : m = n) : (x.res m).val = (y.res n).val := by congr!
@[congr] --how can this help if it is proven with congr?
lemma res_val'_congr (x y : Tree.BodySystemObj T) (h : x = y)
  (h' : m = n) : resEq.val' (x.res m) = resEq.val' (y.res n) := by congr
lemma containsTree.map {x : BodySystemObj S} {y}
  (h : x.containsTree y) (f : S ⟶ T) : (bodySystem.map f x).containsTree (f y) := by
  apply_fun f at h; simp_rw [h, containsTree, resEq.val', bodySystem,
    resEq_map, LenHom.h_length_simp, resEq_len, Subtype.coe_eta]
end BodySystemObj

@[simp] lemma _root_.GaleStewartGame.IsPosition.iff_lenHom
    (p : Player) {S T : Trees} (f : S ⟶ T) x :
  IsPosition (A := no_index _) (f x).val p ↔ IsPosition x.val p := by synth_isPosition
@[simp] lemma _root_.GaleStewartGame.iff_pInv_lenHom
    (p : Player) {S T : Trees} (f : S ⟶ T) x (h : Fixing x.val.length f) :
  IsPosition (A := no_index _) (Tree.pInv f x h).val p ↔ IsPosition x.val p := by synth_isPosition

/-- a partial strategy defined only on positions up to length k -/
def ResStrategy (T : Trees) (p : Player) (k : ℕ) :=
  ∀ x : T, IsPosition x.val p → x.val.length ≤ k → ExtensionsAt x
namespace ResStrategy
@[ext] lemma ext {S S' : ResStrategy T p k} (h : ∀ x hp hl, S x hp hl = S' x hp hl) : S = S' :=
  funext (fun x ↦ funext (fun hp ↦ funext (h x hp)))
@[congr] --simp needs this
lemma eval_val'_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).val' = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).val' := by
  congr!
@[congr]
lemma eval_valT'_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).valT' = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).valT' := by
  congr!
@[congr]
lemma eval_val_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).val = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).val := by
  congr!
def res (h : m ≤ k) (S : ResStrategy T p k) : ResStrategy T p m :=
  fun x hp hl ↦ S x hp (by omega)
@[simp] lemma res_refl (S : ResStrategy T p k) : S.res le_rfl = S := rfl
@[simp] lemma res_trans (m n k) (S : ResStrategy T p k) (mn : m ≤ n) (nk : n ≤ k) :
  (S.res nk).res mn = S.res (mn.trans nk) := rfl

def fromMap (f : S ⟶ T) (h : Tree.Fixing k f := by abstract synth_fixing)
  (S' : ResStrategy S p k) : ResStrategy T p k := fun x hx hl ↦
    ExtensionsAt.map f (x := pInv f x) (y := x) (by simp_rw [cancel_pInv_right])
      (S' _ (by simpa only [iff_pInv_lenHom]) (by simpa only [h_length_pInv]))
@[congr] --simp needs this
lemma fromMap_congr {f g : S ⟶ T}
  (heq : f = g) (hh : Tree.Fixing k f) :
  ResStrategy.fromMap f hh = ResStrategy.fromMap (p := p) (f := g) (h := by subst heq; exact hh) := by
  congr! --could be generated automatically, propositional extensionality
def fromMapInv (f : S ⟶ T) (h : Tree.Fixing (k + 1) f := by abstract synth_fixing)
  (S' : ResStrategy T p k) : ResStrategy S p k := fun y hy hl ↦
    (@Tree.extensionsEquiv _ _ f y (h.mon (by simpa))).symm
    (S' _ (by synth_isPosition) (by simpa only [LenHom.h_length_simp]))
def fromMapEquiv p k (f : S ⟶ T) (h : Tree.Fixing (k + 1) f := by abstract synth_fixing) :
  ResStrategy S p k ≃ ResStrategy T p k where
  toFun := fromMap f
  invFun := fromMapInv f
  left_inv S' := by
    ext1 x _ hl; apply ExtensionsAt.ext_valT'
    simp_rw [fromMapInv, fromMap, extensionsEquiv_symm_val', ExtensionsAt.map_valT', cancel_pInv_left]
  right_inv S' := by
    ext1; apply ExtensionsAt.ext_valT'
    simp_rw [fromMap, fromMapInv, ExtensionsAt.map_valT', extensionsEquiv_symm_val', cancel_pInv_right]
@[simp] lemma res_fromMap {k m} (h : m ≤ k) (f : S ⟶ T) (hf : Fixing k f)
  (S' : ResStrategy S p k) : (fromMap f hf S').res h = (fromMap f) (S'.res h) := by
  ext1; apply ExtensionsAt.ext_valT'; simp [fromMap, res]
@[simp] lemma fromMap_id k (S' : ResStrategy T p k) :
  (fromMap (𝟙 T)) S' = S' := by
  ext1; apply ExtensionsAt.ext_valT'; simp [fromMap]

@[simp] lemma fromMap_comp k {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U)
  (hf : Tree.Fixing k f := by abstract synth_fixing) (hg : Tree.Fixing k g := by abstract synth_fixing)
  (S' : ResStrategy S p k) :
  (fromMap (f ≫ g)) S' = (fromMap g hg) ((fromMap f hf) S') := by
  ext1 x _ hl; apply ExtensionsAt.ext_valT'
  simp_rw [fromMap, ExtensionsAt.map_valT', comp_apply, ← pInv_comp']
lemma fromMap_comp' k {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U) --regression need
  (hf : Tree.Fixing k f) (hg : Tree.Fixing k g) (S' : ResStrategy S p k) :
  (fromMap (f ≫ g)) S' = (fromMap g hg) ((fromMap f hf) S') := fromMap_comp k f g hf hg S'
@[simp] lemma fromMap_valT' {S T : Trees}
  (f : S ⟶ T) (hf : Tree.Fixing k f) (S' : ResStrategy S p k) x hx hl :
  (fromMap f hf S' (f x) (by simp [hx]) (by simp [hl])).valT' = f (S' x hx hl).valT' := by
  ext; simp_rw [fromMap, ExtensionsAt.map_valT', cancel_pInv_left]
end ResStrategy

/-- a strategy as an inverse limit of a sequence of `ResStrategy` -/
@[ext] structure StrategySystem (T : Trees) (p : Player) where
  str : ∀ k, ResStrategy T p k
  con : ∀ k, (str (k + 1)).res (Nat.le_succ k) = str k
@[simp] lemma StrategySystem.con' (S : StrategySystem T p) (h : k ≤ m) :
  (S.str m).res h = S.str k := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h; induction' n with n ih; rfl
  simp_rw [← ih (by simp), Nat.add_succ, ← (S.str (k + n + 1)).res_trans k
    (k + n) (k + n + 1) (by omega) (by omega), S.con]
@[simps] def strategyEquivSystem : Strategy T.2 p ≃ StrategySystem T p where
  toFun S := {
    str := fun _ x h _ ↦ S x h
    con := fun _ ↦ rfl
  }
  invFun S x hp := S.str x.val.length x hp (by omega)
  left_inv _ := rfl
  right_inv S := by
    ext1; ext1; ext1 _ _ hl; simp_rw [← S.con' hl]; rfl

section
variable {A : Type*} {T : tree A} {y : Stream' A}
lemma preStrategy_body (f : PreStrategy T p) : y ∈ body f.subtree
  ↔ ∃ (hy : y ∈ body T), ∀ (x : T), (hp : IsPosition x.val p) → (hb : y ∈ principalOpen x.val) →
    ⟨y.get x.val.length, by apply hy; simp [principalOpen_concat, hb]⟩ ∈ f x hp := by
  constructor <;> intro h
  · use body_mono f.subtree_sub h
    intro x _ hy; specialize h (x ++ [y.get x.val.length]) (by simp [principalOpen_concat, hy])
    apply h.2 List.prefix_rfl
  · intro x hx; have hxT := h.1 _ hx
    use hxT; intro z a hpr hpo
    replace h := h.2 ⟨_, mem_of_append (mem_of_prefix hpr hxT)⟩ hpo
    replace hx := principalOpen_mono hpr hx; rw [principalOpen_concat] at hx
    obtain ⟨hx, rfl⟩ := hx; exact h hx
lemma strategy_body (f : Strategy T p) : y ∈ body f.pre.subtree ↔ y ∈ body T ∧
  ∀ (x : T), (hp : IsPosition x.val p) → y ∈ principalOpen x.val →
  y.get x.val.length = (f x hp).val := by
  simp_rw [preStrategy_body, ← exists_prop, Set.mem_singleton_iff, ← SetCoe.ext_iff (b := f _ _)]
end
def consistent (x : BodySystemObj T) (S : StrategySystem T p) :=
  ∀ (y : T), (hp : IsPosition y.val p) → x.contains y.val
  → x.contains (S.str y.val.length y hp le_rfl).val'
lemma mem_principalOpen_iff_bodySystem_contains {T : Trees} (x : List T.1) (y : body T.2) :
  y.val ∈ principalOpen x ↔ (bodyEquivSystem.hom.app _ y).contains x := by
  constructor <;> intro h
  · apply List.ext_getElem?; intro n; rw [principalOpen_iff_restrict] at h
    simp_rw [bodyEquivSystem_hom_app_res_coe, ← h]
  · rw [h]; simp_rw [bodyEquivSystem_hom_app_res_coe, extend_sub]
lemma bodyEquivSystem_strat {x} (S : StrategySystem T p) :
  x.val ∈ body (strategyEquivSystem.symm S).pre.subtree
  ↔ consistent (bodyEquivSystem.hom.app _ x) S := by
  simp only [strategy_body, Subtype.coe_prop, true_and, consistent]
  show (∀ x : T, _) ↔ _ --add feature that congr! works without this?, (config := {typeEqs := true}) doesn't help
  congr! with y _ hc
  apply mem_principalOpen_iff_bodySystem_contains
  rw [← mem_principalOpen_iff_bodySystem_contains, ExtensionsAt.val', principalOpen_concat]
  simp only [(mem_principalOpen_iff_bodySystem_contains y.val x).mpr hc, true_and]; rfl
lemma bodyEquivSystem_strat' {x} (S : StrategySystem T p) :
  (bodyEquivSystem.inv.app _ x).val ∈ body (strategyEquivSystem.symm S).pre.subtree
  ↔ consistent x S := by
  simp [bodyEquivSystem_strat]
lemma bodyEquivSystem_strat'' {x} (S : Strategy T.2 p) :
  x.val ∈ body S.pre.subtree
  ↔ consistent (bodyEquivSystem.hom.app T x) (strategyEquivSystem S) := by
  simp [← bodyEquivSystem_strat]
end
end GaleStewartGame.Tree
