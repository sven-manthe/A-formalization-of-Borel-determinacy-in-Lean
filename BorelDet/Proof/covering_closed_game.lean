import BorelDet.Proof.covering

namespace GaleStewartGame.BorelDet
open Stream'.Discrete Descriptive Tree
open Classical CategoryTheory
noncomputable section

variable {A : Type*}
structure Hyp (G : Game A) (k : ℕ) where
  closed : IsClosed G.payoff
  pruned : IsPruned G.tree
  nonempty : [] ∈ G.tree
variable {G : Game A} {k : ℕ} (hyp : Hyp G k)
--the second component is the residual tree of valid extensions
set_option linter.unusedVariables false in
def upA (hyp : Hyp G k) := A × tree A
set_option hygiene false
scoped notation "A'" => (upA hyp)
def getTree' (x : List A') := match x.getLast? with
  | none => G.tree
  | some a => a.2
scoped notation "getTree" => (getTree' hyp)
variable {hyp}
@[simp] lemma getTree_nil : getTree ([] : List A') = G.tree := rfl
@[simp] lemma getTree_concat x (a : A') : getTree (x ++ [a]) = a.2 := by simp [getTree']

def LosingCondition (x : List A') (h : x.length = 2 * k + 2) :=
  body (pullSub (getTree x) (x.map Prod.fst)) ∩ G.payoff = ∅ ∧
  ∃ y : subAt (getTree (x.take (2 * k + 1))) [x[2 * k + 1].1],
    getTree x = pullSub (subAt G.tree (x.map Prod.fst ++ y)) y
lemma LosingCondition.concat {x : List A'} {a h} :
  LosingCondition (x ++ [a]) h ↔
  body (pullSub a.2 (x.map Prod.fst ++ [a.1])) ∩ G.payoff = ∅ ∧
  ∃ y : subAt (getTree x) [a.1], a.2
  = pullSub (subAt G.tree (x.map Prod.fst ++ a.1 :: y)) y := by
  unfold LosingCondition; simp at h ⊢; congr! <;> simp [← h]
lemma LosingCondition.of_concat {x : List A'} {a h} (H : LosingCondition (x ++ [a]) h) :
  ∃ y : subAt (getTree x) [a.1], a.2
  = pullSub (subAt G.tree (x.map Prod.fst ++ a.1 :: y)) y := (concat.mp H).2
def WinningCondition (x : List A') (h : x.length = 2 * k + 2) :=
  body (pullSub (getTree x) (x.map Prod.fst)) ⊆ G.payoff ∧
  ∃ S' : QuasiStrategy (subAt (getTree (x.take (2 * k + 1))) [x[2 * k + 1].1]) Player.one,
    getTree x = S'.1.subtree
lemma cast_subtree {A} {T T' : tree A} {p p'} (hT : T = T') (hp : p = p') (S : QuasiStrategy T p) :
  (cast (by rw [hT, hp]) S : QuasiStrategy T' p').1.subtree = S.1.subtree := by subst hT hp; rfl
lemma WinningCondition.concat {x : List A'} {a h} :
  WinningCondition (x ++ [a]) h ↔
  body (pullSub a.2 (x.map Prod.fst ++ [a.1])) ⊆ G.payoff ∧
  ∃ S' : QuasiStrategy (subAt (getTree x) [a.1]) Player.one, a.2
  = S'.1.subtree := by
  simp at h; unfold WinningCondition; simp; intro _
  constructor <;> (
    intro ⟨S, he⟩; use cast (by simp [h]) S
    rw [cast_subtree (by simp [h]) rfl]; simpa)
lemma WinningCondition.of_concat {x : List A'} {a h} (H : WinningCondition (x ++ [a]) h) :
  ∃ S' : QuasiStrategy (subAt (getTree x) [a.1]) Player.one, a.2
  = S'.1.subtree := (concat.mp H).2

def ValidExt (x : List A') (a : A') := [a.1] ∈ getTree x ∧
  if x.length = 2 * k then
    ∃ S : QuasiStrategy (subAt (getTree x) [a.1]) Player.one, a.2 = S.1.subtree
  else if h : x.length = 2 * k + 1 then
    LosingCondition (x ++ [a]) (by simpa) ∨ WinningCondition (x ++ [a]) (by simpa)
  else a.2 = subAt (getTree x) [a.1]
@[simp] lemma validExt_zero {x : List A'} {a : A'} (h : x.length = 2 * k) :
  ValidExt x a ↔ [a.1] ∈ getTree x ∧
  ∃ S : QuasiStrategy (subAt (getTree x) [a.1]) Player.one, a.2 = S.1.subtree := by
  simp [ValidExt, h]
@[simp] lemma validExt_one {x : List A'} {a : A'} (h : x.length = 2 * k + 1) :
  ValidExt x a ↔ [a.1] ∈ getTree x ∧
 (LosingCondition (x ++ [a]) (by simpa) ∨ WinningCondition (x ++ [a]) (by simpa)) := by
  simp [ValidExt, h]
@[simp] lemma validExt_short {x : List A'} {a : A'} (h : x.length < 2 * k) :
  ValidExt x a ↔ [a.1] ∈ getTree x ∧ a.2 = subAt (getTree x) [a.1] := by
  unfold ValidExt; split_ifs <;> (try omega); simp
@[simp] lemma validExt_long {x : List A'} {a : A'} (h : 2 * k + 2 ≤ x.length) :
  ValidExt x a ↔ [a.1] ∈ getTree x ∧ a.2 = subAt (getTree x) [a.1] := by
  unfold ValidExt; split_ifs <;> (try omega); simp

variable (hyp)
/-- the tree of the unraveled game of a closed game -/
def gameTree : tree A' where
  val := {x | List.reverseRecOn x True (fun x a hx ↦ hx ∧ ValidExt x a)}
  property _ := by simp; tauto
set_option linter.unusedVariables false in --include hyp in doesn't suffice
@[simps] def oldAsTrees (hyp : Hyp G k) : Trees := ⟨A, G.tree⟩
@[simps] def gameAsTrees : Trees := ⟨A', gameTree hyp⟩
variable {hyp}
scoped notation "T" => (G.tree)
scoped notation "T'" => (gameTree hyp)
lemma gameTree_ne : [] ∈ T' := by simp [gameTree]
@[simp] lemma gameTree_concat (x : List A') (a : A') :
  x ++ [a] ∈ T' ↔ x ∈ T' ∧ ValidExt x a := by simp [gameTree]
lemma getTree_sub (x : T') :
  getTree x.val ≤ subAt G.tree (x.val.map Prod.fst) := by
  have ⟨x, h⟩ := x; induction' x using List.reverseRecOn with x a ih
  · simp
  · simp at h ⊢; obtain ⟨h, ⟨_, h2⟩⟩ := h; split_ifs at h2
    · obtain ⟨S, h2⟩ := h2; rw [h2, ← subAt_append]; apply le_trans S.1.subtree_sub
      gcongr; exact ih h
    · rcases h2 with h2 | h2
      · obtain ⟨y, h2⟩ := h2.of_concat; rw [h2, List.append_cons, ← subAt_append]
        apply pullSub_subAt
      · obtain ⟨S', h2⟩ := h2.of_concat; rw [h2, ← subAt_append]
        apply le_trans S'.1.subtree_sub
        gcongr; exact ih h
    · rw [h2, ← subAt_append]; gcongr; exact ih h
lemma getTree_ne_and_pruned (x : T') :
  [] ∈ getTree x.val ∧ IsPruned (getTree x.val) := by
  have ⟨x, h⟩ := x; induction' x using List.reverseRecOn with x a ih
  · exact ⟨hyp.nonempty, hyp.pruned⟩
  · simp at h ⊢; obtain ⟨h, ⟨h1, h2⟩⟩ := h; split_ifs at h2
    · obtain ⟨S, h2⟩ := h2; simpa [h2, h1] using S.subtree_isPruned ((ih h).2.sub _)
    · rcases h2 with h2 | h2
      · obtain ⟨⟨y, hy⟩, h2⟩ := h2.of_concat
        simpa [h2] using ⟨getTree_sub ⟨x, h⟩ hy, (hyp.pruned.sub _).pullSub y⟩
      · obtain ⟨S', h2⟩ := h2.of_concat; simpa [h2, h1] using S'.subtree_isPruned ((ih h).2.sub _)
    · simp [h2, h1, IsPruned.sub, ih h]

section
variable {x : T'} {h : x.val.length = 2 * k + 2}
namespace LosingCondition
variable (H : LosingCondition x.val h)
def y : getTree x.val where
  val := H.2.choose.val
  property := by
    obtain ⟨x, hx⟩ := x; rcases x.eq_nil_or_concat' with rfl | ⟨_, _, rfl⟩ <;> simp at h
    conv => lhs; rw [H.2.choose_spec]
    simpa using getTree_sub ⟨_, mem_of_append hx⟩
      (by simpa [- SetLike.coe_mem, h] using H.2.choose.prop)
lemma y_spec : getTree x.val
  = pullSub (subAt G.tree (x.val.map Prod.fst ++ H.y.val)) H.y.val := H.2.choose_spec
end LosingCondition
namespace WinningCondition
variable (H : WinningCondition x.val h)
def S : QuasiStrategy (subAt (getTree (x.val.take (2 * k + 1)))
  [x.val[2 * k + 1].1]) Player.one := H.2.choose
lemma S_spec : getTree x.val = H.S.1.subtree := H.2.choose_spec
end WinningCondition

variable (x h) in
lemma lose_or_win : LosingCondition x.val h ∨ WinningCondition x.val h := by
  let ⟨x, hx⟩ := x; rcases x.eq_nil_or_concat' with rfl | ⟨_, _, rfl⟩ <;> simp at h
  simp [gameTree, h] at hx; tauto
@[simp] lemma not_winning : ¬ WinningCondition x.val h ↔ LosingCondition x.val h := by
  constructor
  · have := lose_or_win x h; tauto
  · intro ⟨H, _⟩ ⟨H', _⟩
    rw [← Set.inter_eq_left, H, Eq.comm, ← Set.not_nonempty_iff_eq_empty,
      IsPruned.body_ne_iff_ne] at H'
    · apply H'; simp; exact (getTree_ne_and_pruned x).1
    · apply IsPruned.pullSub; exact (getTree_ne_and_pruned x).2
@[simp] lemma not_losing : ¬ LosingCondition x.val h ↔ WinningCondition x.val h := by
  rw [← not_iff_not, not_not, not_winning]
end

variable (hyp)
def treeHom : gameAsTrees hyp ⟶ oldAsTrees hyp where
  toFun x := ⟨x.val.map Prod.fst, by
    have h : [] ∈ subAt _ _ := getTree_sub x (getTree_ne_and_pruned x).1
    simpa using h⟩
  monotone' _ _ h := h.map Prod.fst
  h_length := by simp
scoped notation "π" => (treeHom hyp)
def pInvTreeHom_map (x : List A) : List A' := x.zipInitsMap (fun a y ↦ (a, (G.residual y).tree))
variable {hyp}
@[simp] lemma treeHom_val x : (π x).val = x.val.map Prod.fst := rfl
@[simp] lemma treeHom_body (x : body T') : ((bodyFunctor.map π) x).val = x.val.map Prod.fst := by
  ext; apply Option.some_injective; rw [bodyMap_spec_res']; simp
lemma T'_snd_small' (x : T') (h : x.val.length ≤ 2 * k) :
  getTree x.val = subAt G.tree (x.val.map Prod.fst) := by
  have ⟨x, hx⟩ := x
  induction' x using List.reverseRecOn with x a ih <;> simp at h ⊢
  simp (disch := omega) at hx
  rw [hx.2.2, ih hx.1 (by simp; omega), subAt_append]
lemma T'_snd_small {x a} (h : x ++ [a] ∈ T') (h' : x.length < 2 * k) :
  a.2 = (G.residual (x.map Prod.fst ++ [a.1])).tree := by
  simpa using T'_snd_small' ⟨_, h⟩ (by simpa using h')
@[simp] lemma pInvTreeHom_map_nil : pInvTreeHom_map hyp [] = [] := by simp [pInvTreeHom_map]
@[simp] lemma pInvTreeHom_map_concat (x : List A) (a : A) :
  pInvTreeHom_map hyp (x ++ [a])
  = pInvTreeHom_map hyp x ++ [⟨a, (G.residual (x ++ [a])).tree⟩] := by simp [pInvTreeHom_map]
@[simp, simp_lengths] lemma pInvTreeHom_map_len (x : List A) :
  (pInvTreeHom_map hyp x).length = x.length := by simp [pInvTreeHom_map]
@[simp] lemma getTree_pInvTreeHom_map (x : List A) :
  getTree (pInvTreeHom_map hyp x) = (G.residual x).tree := by
  rcases x.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩ <;> simp
variable (hyp)
def pInvTreeHom : (Tree.res (2 * k)).obj ⟨_, T⟩ ⟶ (Tree.res (2 * k)).obj ⟨_, T'⟩ where
  toFun x := ⟨pInvTreeHom_map hyp x.val, by
    have ⟨x, h⟩ := x; induction' x using List.reverseRecOn with x a ih
    · simpa using ⟨gameTree_ne, by simp⟩
    · specialize ih (mem_of_append h)
      simp [res] at ih ⊢
      have : x.length + 1 ≤ 2 * k := by
        simpa only [List.length_append, List.length_singleton] using h.2
      use ⟨ih.1, by simpa (disch := simp only [pInvTreeHom_map_len]; omega) using h.1⟩⟩
  monotone' x y h := h.zipInitsMap _ _ _
  h_length := by simp_rw [res_obj_fst, pInvTreeHom_map_len, implies_true]
@[simp] lemma pInvTreeHom_val (x : (Tree.res (2 * k)).obj ⟨_, T⟩) :
  (pInvTreeHom hyp x).val = pInvTreeHom_map hyp x.val := rfl
def treeHomRes : (Tree.res (2 * k)).obj ⟨_, T'⟩ ≅ (Tree.res (2 * k)).obj ⟨_, T⟩ where
  hom := (Tree.res (2 * k)).map π
  inv := pInvTreeHom hyp
  hom_inv_id := by
    ext1 ⟨x, h⟩; ext1
    --erw needed since defining T' as Tree instead of Trees
    simp_rw [CategoryTheory.comp_apply, pInvTreeHom_val, res_val]
    erw [treeHom_val]; simp_rw [CategoryTheory.id_apply]
    induction' x using List.reverseRecOn with x a ih
    · simp
    · simp_rw [res.val'_coe] at *
      simp_rw [List.map_append, List.map_cons, List.map_nil,
        pInvTreeHom_map_concat, ih (mem_of_append h)]
      show _ = _ ++ [(a.1, a.2)]; rw [T'_snd_small h.1 (by simpa using h.2)]
  inv_hom_id := by
    ext1 ⟨x, h⟩; ext1
    simp; erw [treeHom_val]; simp [pInvTreeHom_map, ← List.zipInitsMap_map]
instance treeHom_fixing : Tree.Fixing (2 * k) π := ⟨Iso.isIso_hom (treeHomRes hyp)⟩
@[simp] lemma pInv_treeHom_val x (h : x.val.length ≤ 2 * k) :
  (pInv π x).val = pInvTreeHom_map hyp x.val := by
  show _ = (res.val' (pInvTreeHom hyp ⟨x.val, ⟨x.prop, h⟩⟩)).val
  congr 1; apply Fixing.inj π _
  show _ = res.val' ((treeHomRes hyp).hom ((treeHomRes hyp).inv _)); simp

variable {hyp}
lemma gameTree_isPruned : IsPruned <| gameTree hyp := by
  intro ⟨x, hx⟩; obtain ⟨hne, hPr⟩ := (getTree_ne_and_pruned ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := hPr ⟨[], hne⟩; dsimp at ha
  by_cases hlen : x.length = 2 * k + 1; swap
  use (a, subAt (getTree x) [a]); by_cases hlen' : x.length = 2 * k; swap
  · simpa [hx, ValidExt, hlen, hlen']
  · simp [hx, ValidExt, hlen', ha]
    use ⟨⊤, PreStrategy.top_isQuasi (hPr.sub _)⟩, PreStrategy.top_subtree.symm
  · simp only [ExtensionsAt, upA, nonempty_subtype, Prod.exists]; use a
    conv => rhs; intro b; rw [gameTree_concat]; simp [hlen, hx, ha]
    simp_rw [exists_or, LosingCondition.concat, WinningCondition.concat, exists_exists_and_eq]
    by_cases h : ∃ y : body (subAt (getTree x) [a]),
      x.map Prod.fst ++ [a] ++ₛ y.val ∉ Subtype.val '' G.payoff
    · left; have ⟨y, hy⟩ := h
      rw [← (Game.isClosed_image_payoff.mp hyp.closed).closure_eq,
        mem_closure_iff_nhds_basis (hasBasis_principalOpen' (2 * k + 1 + 1) _)] at hy
      simp at hy; obtain ⟨_, hn, hy⟩ := hy; obtain ⟨n, rfl⟩ := le_iff_exists_add.mp hn
      use body.take n y; simp_rw [pullSub_body, Set.image_image, ← Set.subset_empty_iff]
      rintro x ⟨⟨z, _, rfl⟩, ⟨⟨x', hx'⟩, hxp, rfl⟩⟩; apply hy _ hx' hxp; use z
      rw [← hlen, ← x.length_map Prod.fst, add_assoc, ← Stream'.append_take, add_comm, Stream'.take_succ]
      simp [Stream'.cons_append_stream]
    · right; use ⟨⊤, PreStrategy.top_isQuasi (hPr.sub _)⟩; simpa [Set.subset_def] using h

variable (hyp) in
@[simps] def game : Game A' where
  tree := T'
  payoff := (bodyFunctor.map π)⁻¹' G.payoff
scoped notation "G'" => (game hyp)
lemma getTree_eq' (x : List A') (h : x ∈ T') : getTree x
  = subAt (getTree (x.take (2 * k + 2))) ((x.drop (2 * k + 2)).map Prod.fst) := by
  rcases le_or_gt x.length (2 * k + 2) with h | h
  · simp [List.take_of_length_le h, List.drop_eq_nil_iff.mpr h]
  · have hex : ∃ y z, x = y ++ z ∧ y.length = 2 * k + 2 :=
      ⟨x.take (2 * k + 2), x.drop (2 * k + 2), by simpa using h.le⟩
    obtain ⟨x, y, rfl, hxl⟩ := hex; clear h
    induction' y using List.reverseRecOn with y a ih
    · simp [← hxl]
    · specialize ih (mem_of_append (by simpa))
      simp [← hxl, ← subAt_append] at ih ⊢; rw [← ih, ← List.append_assoc, getTree_concat]
      simp [← List.append_assoc] at h; rw [validExt_long (by simp; omega)] at h; exact h.2.2
lemma getTree_eq (x : T') : getTree x.val
  = subAt (getTree (x.val.take (2 * k + 2))) ((x.val.drop (2 * k + 2)).map Prod.fst) :=
  getTree_eq' x.val x.prop
lemma mem_getTree (x : T') : x.val.map Prod.fst ∈
  pullSub (getTree (x.val.take (2 * k + 2))) ((x.val.take (2 * k + 2)).map Prod.fst) := by
  have h := by simpa [getTree_eq] using (getTree_ne_and_pruned x).1
  constructor
  · simp [List.prefix_take_iff, List.take_prefix]
  · simp at h ⊢; rcases le_or_gt x.val.length (2 * k + 2) with hl | hl
    · simp [hl]; rw [List.drop_eq_nil_of_le (by simp)]; exact mem_of_append h
    · simpa [hl.le]

lemma wins_iff_answer (x : body (G').tree) :
  x ∈ (G').payoff ↔ WinningCondition (x.val.take (2 * k + 2)) (by simp) := by
  have hmem : (bodyFunctor.map π x).val ∈ ((x.val.take (2 * k + 2)).map Prod.fst ++ₛ ·)
    '' body (getTree (x.val.take (2 * k + 2))) := by
    use (x.val.drop (2 * k + 2)).map Prod.fst
    simp [← Stream'.map_append_stream, - Function.iterate_succ]
    apply mem_body_of_take 0; intro n _
    simp_rw [← Stream'.map_take, Stream'.take_drop, List.map_drop]
    simpa using (mem_getTree (body.take (2 * k + 2 + n) x)).2
  constructor <;> intro h
  · apply (not_losing (x := body.take (2 * k + 2) x)).mp
    intro ⟨h', _⟩; rw [← Set.subset_empty_iff] at h'
    exact h' (a := (bodyFunctor.map π x).val) ⟨by simpa using hmem, by simpa [- treeHom_body]⟩
  · simp; rw [← Subtype.val_injective.mem_set_image]; exact h.1 (by simpa using hmem)
instance : TopologicalSpace A' := ⊥
instance : DiscreteTopology A' where eq_bot := rfl
lemma payoff_clopen : IsClopen (G').payoff := by
  let f : (Stream' A') → Bool := (fun x ↦ ∃ h, WinningCondition x h) ∘ Stream'.take (2 * k + 2)
  suffices Continuous f by
    convert ((isClopen_discrete {true}).preimage this).preimage continuous_subtype_val
    ext; simp [- game_payoff, - game_tree, wins_iff_answer, f]
  --TODO generalize, how to phrase?
  let _ : TopologicalSpace (List A') := ⊥
  have : DiscreteTopology (List A') := ⟨rfl⟩
  apply continuous_bot.comp
  rw [(isTopologicalBasis_singletons _).continuous_iff]
  simp; intro x; by_cases h : x.length = 2 * k + 2
  · convert principalOpen_isOpen x; ext; simp [principalOpen_iff_restrict, h, Eq.comm] --would (a = b <-> b = c) <-> (a = c) be a good simp lemma?
  · convert isOpen_empty; rw [← Set.subset_empty_iff]; intro x hx
    apply h; simpa using congr_arg List.length hx.symm


lemma T'_snd_medium' (x : T') (h : x.val.length = 2 * k + 1) :
  ∃ S : QuasiStrategy (G.residual (x.val.map Prod.fst)).tree Player.one,
  getTree x.val = S.1.subtree := by
  have ⟨x, hx⟩ := x; rcases x.eq_nil_or_concat' with rfl | ⟨x, a, rfl⟩ <;> simp at h
  simp [ValidExt, h] at hx; convert hx.2.2
  simp_rw [Game.residual_tree, getTree_concat]
  rw [T'_snd_small' ⟨x, hx.1⟩ (by simp [h]), subAt_append, List.map_append, List.map_singleton]
@[simp] lemma treeHom_extensions_val {x} (a : ExtensionsAt x) {y} (h : π x = y) :
  (ExtensionsAt.map π h a).val = a.val.1 := by
  have : (ExtensionsAt.map π h a).val'[x.val.length]
    = (a.val'.map (α := A') Prod.fst)[x.val.length] := by congr; simp
  conv at this => rhs; simp
  rwa [(ExtensionsAt.map π h a).val'_get_last_of_eq (by simp [← h])] at this
lemma extensionsAt_ext_fst {x : (G').tree} (a b : ExtensionsAt x)
  (hx : 2 * k + 2 ≤ x.val.length) (h : a.val.1 = b.val.1) : a = b := by
  ext; apply Prod.ext h
  have ha := a.prop; have hb := b.prop; simp [hx] at ha hb
  rw [ha.2, hb.2, h]

lemma getTree_lost
  {x : (G').tree} (y : (G').tree) (h : x.val <+: y.val) (hxl : x.val.length = 2 * k + 2) --TODO synth le fails since update
  (hL : G.WonPosition (y.val.map Prod.fst) (Player.one.residual y.val)) :
  LosingCondition (hyp := hyp) x hxl := by
  apply not_winning.mp; intro hW
  simp (config := {contextual := true}) [Game.wonPosition_iff_disjoint, Player.residual] at hL
  obtain ⟨a, ha1, ha2⟩ := isPruned_iff_principalOpen_ne.mp gameTree_isPruned y
  refine hL.subset (a := (bodyFunctor.map π ⟨a, ha2⟩).val) ⟨?_, hW.1 ?_⟩
  · simp [principalOpen_iff_restrict, ← Stream'.map_take]; congr; rwa [← principalOpen_iff_restrict]
  · simp; use (a.map Prod.fst).drop (2 * k + 2)
    have hax : x.val = a.take (2 * k + 2) := by
      rw [(principalOpen_iff_restrict _ _).mp (principalOpen_mono h ha1)]; simp [hxl]
    constructor
    · apply mem_body_of_take 0; intro n _; rw [Stream'.take_drop]
      simpa [hax, Stream'.map_take] using (mem_getTree ⟨a.take (2 * k + 2 + n), take_mem_body ha2 _⟩).2
    · rw [hax, Stream'.map_take, Stream'.append_take_drop]
lemma LosingCondition.not_lost_short {x : (G').tree} (hxl : 2 * k + 2 ≤ x.val.length)
  (H : LosingCondition (Tree.take (2 * k + 2) x).val (by simpa))
  (hnL : ¬ G.WonPosition (x.val.map Prod.fst) (Player.one.residual x.val)) :
  x.val.length + 1 ≤ 2 * k + 2 + H.y.val.length := by
  by_contra hlen; simp [Nat.lt_iff_add_one_le] at hlen; apply hnL
  have hx := mem_getTree x; erw [H.y_spec] at hx
  rw [pullSub_append, mem_pullSub_long (by simpa [hxl])] at hx
  obtain ⟨z, _, hze⟩ := hx; have hW := H.1
  simp_rw [H.y_spec, pullSub_append, pullSub_body, subAt_body] at hW
  have := Game.WonPosition.extend z (G := G) (p := Player.one.residual (x.val.map Prod.fst ++ z))
    (x := (x.val.map Prod.fst).take (2 * k + 2) ++ H.y.val) (by --TODO extract lemmas
    rw [Game.wonPosition_iff_disjoint]
    simp_rw [Set.image_preimage_eq_range_inter, Set.inter_assoc,
      Set.image_val_inter_self_right_eq_coe, take_coe, List.map_take] at hW
    convert hW using 3; convert Player.payoff_zero; synth_isPosition)
  rw [← List.map_take, ← hze] at this; convert this using 1; synth_isPosition
lemma extensionsAt_eq_of_lost
  {x : (G').tree} (y : (G').tree) (h : x.val <+: y.val) (hxl : 2 * k + 2 ≤ x.val.length)
  (hnL : ¬ G.WonPosition (x.val.map Prod.fst) (Player.one.residual x.val))
  (hL : G.WonPosition (y.val.map Prod.fst) (Player.one.residual y.val))
  {a b : ExtensionsAt x} : a = b := by
  let H := getTree_lost y (x := Tree.take (2 * k + 2) x)
    ((x.val.take_prefix _).trans h) (by simpa) hL
  have hlen := H.not_lost_short hxl hnL
  apply extensionsAt_ext_fst _ _ hxl
  have ha := mem_getTree a.valT'; have hb := mem_getTree b.valT'
  have Hys := H.y_spec; simp at Hys
  simp (disch := omega) [ExtensionsAt.val', List.take_append_of_le_length, Hys] at ha hb
  rw [mem_pullSub_short (by simpa [hxl])] at ha hb
  rcases List.prefix_or_prefix_of_prefix ha.1 hb.1 with h | h <;> [skip; symm] <;>
    simpa using h.eq_of_length (by simp)

end
end GaleStewartGame.BorelDet
