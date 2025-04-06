import BorelDet.Game.gale_stewart
import BorelDet.Proof.build_levelwise

namespace GaleStewartGame
open Classical CategoryTheory
open Descriptive Tree Stream'.Discrete

noncomputable section
variable {k m n : ℕ} {p : Player}
namespace Covering
/-- a tree that is pruned and nonempty as required for determinacy -/
def PTrees := Σ' (T : Trees), IsPruned T.2 ∧ [] ∈ T.2
@[simp] lemma pTrees_isPruned (T : PTrees) : IsPruned T.1.2 := T.2.1
@[simp] lemma pTrees_ne (T : PTrees) : [] ∈ T.1.2 := T.2.2
end Covering
namespace ResStrategy
variable {T : Covering.PTrees} (S : ResStrategy T.1 p k)
def choose_succ : ResStrategy T.1 p m :=
  fun x hp _ ↦ if h' : x.val.length ≤ k then S x hp h' else choice (T.2.1 x)
@[simp] lemma res_choose_succ (h : k ≤ m) : S.choose_succ.res h = S := by
  ext _ _ hl; simp [choose_succ, res, hl]
lemma res_surjective (h : m ≤ k) : (res h (T := T.1) (p := p)).Surjective :=
  fun S ↦ ⟨_, S.res_choose_succ h⟩
@[simps] def choose_system : StrategySystem T.1 p where
  str k := S.choose_succ
  con k := by ext x; simp [choose_succ, res]
lemma choose_system_self : S.choose_system.str k = S := by ext _ _ hl; simp [choose_succ, hl]
lemma str_surjective : (fun (S : StrategySystem T.1 p) ↦ S.str k).Surjective :=
  fun S ↦ ⟨_, S.choose_system_self⟩
end ResStrategy
namespace Covering
structure PTreesS where
  tree : PTrees
/-- a map of strategies whose output on the first k levels only depends on
  the input on the first k levels-/
@[ext] structure LvlStratHom (T U : PTreesS) where
  toFun : ∀ p k, ResStrategy T.tree.1 p k → ResStrategy U.tree.1 p k
  con : ∀ p {k m} (h : m ≤ k) S, (toFun p k S).res h = toFun p m (S.res h)
def LvlStratHom.id (T : PTreesS) : LvlStratHom T T where
  toFun p k := _root_.id
  con := by simp
def LvlStratHom.comp {T U V : PTreesS} (g : LvlStratHom U V) (f : LvlStratHom T U) :
  LvlStratHom T V where
  toFun p k := g.toFun p k ∘ f.toFun p k
  con := by simp [g.con, f.con]
instance : Category PTreesS where
  Hom := LvlStratHom
  id := LvlStratHom.id
  comp f g := LvlStratHom.comp g f
@[simp] lemma LvlStratHom.id_toFun (T : PTreesS) :
  LvlStratHom.toFun (𝟙 T) p k = _root_.id := rfl
@[simp] lemma LvlStratHom.comp_toFun {T U V : PTreesS} (f : T ⟶ U) (g : U ⟶ V) :
  LvlStratHom.toFun (f ≫ g) p k = LvlStratHom.toFun g p k ∘ LvlStratHom.toFun f p k := rfl
@[ext] lemma LvlStratHom.ext' {T U : PTreesS} {f g : T ⟶ U} (h : f.toFun = g.toFun) : f = g :=
  LvlStratHom.ext h
def LvlStratHom.system (p : Player) : PTreesS ⥤ Type* where
  obj T := StrategySystem T.tree.1 p
  map f S := {
    str := fun k ↦ f.toFun p k (S.str k),
    con := by simp [f.con]
  }
def LvlStratHom.global (p : Player) : PTreesS ⥤ Type* where
  obj T := Strategy T.tree.1.2 p
  map f S := strategyEquivSystem.symm ((system p).map f (strategyEquivSystem S))
  map_id _ := rfl
  map_comp _ _ := by ext; simp only [system, comp_toFun, Function.comp_apply,
    types_comp_apply, Equiv.apply_symm_apply]

def bodyLiftExists {T U : PTrees} (toHom : T.1 ⟶ U.1) (str : PTreesS.mk T ⟶ PTreesS.mk U) :=
  ∀ {p S} (y : body ((LvlStratHom.global p).map str S).pre.subtree),
  ∃ x : body S.pre.subtree,
    (Tree.bodyFunctor.map toHom ⟨x, body_mono S.pre.subtree_sub x.prop⟩).val
    = y.val
lemma bodyLiftExists_iff_system
  {T U : PTrees} (toHom : T.1 ⟶ U.1) (str : PTreesS.mk T ⟶ PTreesS.mk U) :
  bodyLiftExists toHom str ↔ ∀ {p S} (y : bodySystem.obj U.1),
  consistent y ((LvlStratHom.system p).map str S) →
  ∃ x : bodySystem.obj T.1, consistent x S ∧ bodySystem.map toHom x = y := by
  constructor <;> intro h p S y
  · intro yc; obtain ⟨S, rfl⟩ := strategyEquivSystem.surjective S
    rw [← bodyEquivSystem_strat'] at yc; obtain ⟨x, hx⟩ := h ⟨_, yc⟩
    use bodyEquivSystem.hom.app _ ⟨x.val, body_mono S.pre.subtree_sub x.prop⟩
    constructor; exact (bodyEquivSystem_strat _).mp x.prop
    apply ((isIso_iff_bijective (bodyEquivSystem.inv.app _)).mp inferInstance).1
    dsimp; ext; rw [← hx, naturality_apply_types, FunctorToTypes.hom_inv_id_app_apply]
  · let y' : Tree.bodyFunctor.obj U.1 := ⟨y.val, body_mono (PreStrategy.subtree_sub _) y.prop⟩
    obtain ⟨x, ⟨hxc, hxe⟩⟩ := h
      (bodyEquivSystem.hom.app _ y') <| (bodyEquivSystem_strat _).mp y.prop
    use ⟨(bodyEquivSystem.inv.app _ x).val, by apply (bodyEquivSystem_strat'' _).mpr; simp [hxc]⟩
    obtain ⟨y, hy⟩ := ((isIso_iff_bijective (bodyEquivSystem.inv.app _)).mp inferInstance).2 y'
    simp [← hy] at hxe; subst hxe; show _ = y'.val; rw [← hy, naturality_apply_types]; rfl

end Covering
/-- a covering used in the proof of Borel determinacy, given by a length preserving map of nodes
and a map of strategies and satisfying a lifting condition on plays consistent with the
strategy -/
@[ext (flat := false)] structure Covering (T U : Covering.PTrees) where
  toHom : T.1 ⟶ U.1
  str : Covering.PTreesS.mk T ⟶ Covering.PTreesS.mk U
  h_body : Covering.bodyLiftExists toHom str
namespace Covering
instance : Category PTrees where
  Hom := Covering
  id T := ⟨𝟙 T.1, LvlStratHom.id _, fun y ↦ ⟨y, by simp⟩⟩
  comp f g := ⟨f.toHom ≫ g.toHom, f.str ≫ g.str, fun x ↦ by as_aux_lemma =>
    obtain ⟨y, hy⟩ := g.h_body (cast (by simp; rfl) x); obtain ⟨z, hz⟩ := f.h_body y
    use z
    simp only [FunctorToTypes.map_comp_apply, bodyFunctor, bodyPre, set_coe_cast] at hz hy
    simp_rw [FunctorToTypes.map_comp_apply, bodyFunctor, bodyPre, hz, hy]⟩
def PTreeForget : PTrees ⥤ Trees where
  obj T := T.1
  map f := f.toHom
@[simp, simp_lengths] lemma id_covering_toHom (T : PTrees) :
  Covering.toHom (𝟙 T) = 𝟙 _ := rfl
@[simp] lemma id_covering_str (T : PTrees) :
  Covering.str (𝟙 T) = 𝟙 _ := rfl
@[simp, simp_lengths] lemma comp_covering_toHom {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V) :
  (f ≫ g).toHom = f.toHom ≫ g.toHom := rfl
@[simp] lemma comp_covering_str {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V) :
  (f ≫ g).str = f.str ≫ g.str := rfl
lemma comp_covering_str_apply (S T U : PTrees) (f : S ⟶ T) (g : T ⟶ U) A :
  (f ≫ g).str.toFun p k A = g.str.toFun p k (f.str.toFun p k A) := by dsimp
@[ext] lemma ext' {T U : PTrees} {f g : T ⟶ U} (h1 : f.toHom = g.toHom)
  (h2 : f.str = g.str) : f = g := Covering.ext h1 h2

def Fixing k {T U : PTrees} (f : T ⟶ U) :=
  ∃ _ : Tree.Fixing k f.toHom, ∀ p, f.str.toFun p k = ResStrategy.fromMap f.toHom
@[simp] lemma fixing_id k T : Fixing k (𝟙 T) := by
  use (by synth_fixing); intros; ext; simp
lemma fixing_comp k {T U V : PTrees} (f : T ⟶ U) (g : U ⟶ V)
  (hf : Fixing k f) (hg : Fixing k g) : Fixing k (f ≫ g) := by
  have _ := hf.1; have _ := hg.1
  use (by simp [Tree.Fixing]; infer_instance)
  intros; ext; simp [hf.2, hg.2]
lemma fixing_snd_mon {k m} (hm : k ≤ m) {T U : PTrees} (f : T ⟶ U)
  (h : Fixing m f) (p : Player) :
  f.str.toFun p k = ResStrategy.fromMap (f := f.toHom) (h := h.1.mon hm) := by
  ext S'; obtain ⟨S', rfl⟩ := ResStrategy.res_surjective hm S'
  have hs := by simpa using congr_arg (ResStrategy.res hm) (congr_fun (h.2 p) S')
  rw [← hs, f.str.con]
lemma fixing_mon {S T} (f : S ⟶ T) (h : Fixing k f) (hn : n ≤ k) :
  Fixing n f := ⟨h.1.mon hn, fun _ ↦ fixing_snd_mon hn _ h _⟩

def Games := Σ' (A : Type*) (G : Game A), IsPruned G.tree ∧ [] ∈ G.tree
@[simp] lemma games_isPruned (G : Games) : IsPruned G.2.1.tree := G.2.2.1
@[simp] lemma games_ne (G : Games) : [] ∈ G.2.1.tree := G.2.2.2
instance (G : Games) : TopologicalSpace G.1 := ⊥
instance (G : Games) : DiscreteTopology G.1 where eq_bot := rfl
abbrev Games.tree (G : Games) : PTrees := ⟨⟨G.1, G.2.1.tree⟩, G.2.2⟩
@[ext] structure Games.Covering (G' : Games) (G : Games) extends
  GaleStewartGame.Covering G'.tree G.tree where
  hpre : (Tree.bodyFunctor.map toHom)⁻¹' (G.2.1.payoff) = G'.2.1.payoff
@[simp] lemma covering_hpre_pl {G' G} (f : Games.Covering G' G) (p : Player) :
  (Tree.bodyFunctor.map f.toHom)⁻¹' (p.payoff G.2.1) = p.payoff G'.2.1 := by
  cases p <;> simp [f.hpre]
lemma covering_winning {G' G} (f : Games.Covering G' G) {p : Player}
  {S : Strategy G'.tree.1.2 p} (h : S.pre.IsWinning) :
  ((LvlStratHom.global _).map f.str S).pre.IsWinning := by
  intro y hy; obtain ⟨x, rfl⟩ := f.h_body ⟨y, hy⟩
  simp_rw [← Set.mem_preimage, Set.preimage_image_eq _ Subtype.val_injective,
    covering_hpre_pl f, ← Subtype.val_injective.mem_set_image]
  exact h x.prop

def Games.IsUnravelable G := ∀ k, ∃ (G' : Games) (f : Games.Covering G' G),
  Fixing k f.toCovering ∧ IsClopen G'.2.1.payoff
lemma Games.IsUnravelable.isDetermined {G : Games} (h : G.IsUnravelable) :
  G.2.1.IsDetermined :=
  let ⟨_, f, _, h⟩ := h 0
  let ⟨p, s, hw⟩ := Game.gale_stewart h.1 (games_isPruned _)
  ⟨p, ⟨(LvlStratHom.global p).map f.str s, covering_winning f hw⟩⟩

end Covering
end
end GaleStewartGame
