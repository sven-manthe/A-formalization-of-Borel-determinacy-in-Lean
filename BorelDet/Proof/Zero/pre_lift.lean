import BorelDet.Proof.covering_closed_game
import BorelDet.Proof.win_asap

namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section

variable (hyp) in
@[ext] structure PreLift where
  x : T
  hlvl : 2 * k + 1 ≤ x.val.length (α := no_index _)
  R : ResStrategy ⟨_, T'⟩ Player.zero (2 * k)
variable (H : PreLift hyp)
namespace PreLift
attribute [simp] hlvl
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
def liftShort : T' := (H.R (pInv π (Tree.take (2 * k) H.x))
  (by have := H.hlvl; synth_isPosition) (by simp)).valT'
@[simp, simp_lengths] lemma liftShort_length :
  H.liftShort.val.length (α := no_index _) = 2 * k + 1 := by simp [liftShort]
lemma getTree_fair {y} {a} (hy : y ∈ getTree H.liftShort.val)
  (hp : IsPosition y Player.zero) (ha : H.liftShort.val.map Prod.fst ++ (y ++ [a]) ∈ T) :
  y ++ [a] ∈ getTree H.liftShort.val := by
  obtain ⟨S, hS⟩ := T'_snd_medium' H.liftShort H.liftShort_length
  simp_rw [hS] at hy ⊢; rwa [S.1.subtree_fair ⟨y, hy⟩ hp]

@[simps (config := {isSimp := false})] def game : Game A where
  tree := getTree H.liftShort.val
  payoff := Subtype.val⁻¹' (Subtype.val '' (G.residual (H.x.val.take (2 * k + 1))).payoffᶜ)
lemma game_tree_sub : H.game.tree ≤ subAt G.tree (H.liftShort.val.map Prod.fst) :=
  getTree_sub H.liftShort
lemma game_pruned : IsPruned H.game.tree := (getTree_ne_and_pruned _).2
lemma game_closed : IsClosed H.game.payoff := by
  apply IsClosed.preimage continuous_subtype_val
  rw [← (Topology.IsClosedEmbedding.subtypeVal (body_isClosed _)).isClosed_iff_image_isClosed,
    G.residual_payoff_odd _ (by simp [Nat.add_mod]), compl_compl]
  exact hyp.closed.preimage <| body.append_con _

@[simps] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : PreLift hyp where
  x := Tree.take n H.x
  hlvl := by simp [h]
  R := H.R
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1 <;> [ext1; skip] <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by abstract omega) := by
  ext1 <;> simp [min_comm]
@[simp] lemma liftShort_take h : (H.take n h).liftShort = H.liftShort := by
  ext1; simp [liftShort, (by omega : 2 * k ≤ n)]
@[simp] lemma game_take h : (H.take n h).game = H.game := by
  ext <;> simp [game_tree, game_payoff, List.take_take, h]

@[simps] instance : LE (PreLift hyp) where
  le p q := q.take p.x.val.length p.hlvl = p
lemma length_mono {p q : PreLift hyp} (h : p ≤ q) : p.x.val.length ≤ q.x.val.length := by --why not valid gcongr lemma?
  rw [← h]; simp
instance : PartialOrder (PreLift hyp) where
  le_refl := by simp
  le_trans _ _ _ pq qr := by have := length_mono pq; rw [← qr] at pq; simpa [this] using pq
  le_antisymm _ _ pq qp := by
    ext1 <;> [ext1; skip] <;> rw [← pq]
    · simpa using length_mono qp
    · simp
lemma take_le {h} : H.take n h ≤ H := by
  dsimp [LE.le]; simp_rw [List.length_take]
  by_cases H.x.val.length ≤ n <;> [rw [take_of_length_le, take_of_length_le]; congr] <;> omega
@[simp] lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n := by
  (conv => lhs; dsimp [LE.le]); simp [PreLift.ext_iff]

def ConShort := H.x.val[2 * k]'H.hlvl = H.liftShort.val[2 * k].1
@[simp] lemma conShort_iff_take h : (H.take n h).ConShort ↔ H.ConShort := by
  simp [ConShort, List.getElem_take']
def ConLong := H.x.val.drop (2 * k + 1) ∈ H.game.tree
lemma conLong_take {h} (h' : H.ConLong) : (H.take n h).ConLong := by
  simpa [PreLift.ConLong, List.drop_take] using take_mem ⟨_, h'⟩
end PreLift
variable (hyp) in
@[ext (flat := false)] structure Lift extends PreLift hyp where
  h'lvl : 2 * k + 2 ≤ toPreLift.x.val.length (α := no_index _)
  conShort : toPreLift.ConShort
instance : PartialOrder (Lift hyp) where
  le p q := p.toPreLift ≤ q.toPreLift
  le_refl _ := le_rfl (α := PreLift hyp)
  le_trans _ _ _ := le_trans (α := PreLift hyp)
  le_antisymm _ _ pq qp := Lift.ext (le_antisymm pq qp)
namespace Lift
variable (H : Lift hyp)
def Lost' := G.WonPosition H.x.val (Player.one.residual H.x.val)
def Losable := H.ConLong ∧ WinningPrefix H.game Player.one (H.x.val.drop (2 * k + 1))
def Winnable := ¬ WinningPrefix H.game Player.one (H.x.val.drop (2 * k + 1))
lemma Winnable.conLong (h : H.Winnable) : H.ConLong := byContradiction fun h' ↦
  h (winningPrefix_of_not_mem H.game Player.one h')

attribute [simp] h'lvl
@[simp] lemma liftShort_val_map :
  H.liftShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 1) := by
  rw [H.liftShort.val.eq_take_concat (2 * k) (by simp)]
  conv => rhs; rw [(H.x.val.take (2 * k + 1)).eq_take_concat (2 * k) (by simp),
    List.getElem_take, H.conShort]
  simp only [PreLift.liftShort, ExtensionsAt.valT'_coe, List.map_append, List.map_cons,
    List.map_nil, List.take_take, List.append_cancel_right_eq]
  rw [ExtensionsAt.val'_take_of_eq _ (by simp)]; show (π _).val = _; simp
@[simp] lemma liftShort_lift : π H.liftShort = Tree.take (2 * k + 1) H.x := by ext; simp
def liftNode : A := H.x.val[2 * k + 1]

@[simps toPreLift] def take (n : ℕ) (h : 2 * k + 2 ≤ n) : Lift hyp where
  toPreLift := H.toPreLift.take n (by omega)
  h'lvl := by simpa
  conShort := by simpa using H.conShort
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply PreLift.take_of_length_le <;> omega
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.h'lvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp
@[simp] lemma liftNode_take h : (H.take n h).liftNode = H.liftNode := by
  simp [liftNode, List.getElem_take']
lemma eq_take_of_le {p q : Lift hyp} (h : p ≤ q) :
  q.take p.x.val.length (by simp) = p := Lift.ext h
lemma take_le {h} : H.take n h ≤ H := H.toPreLift.take_le (h := by omega)
@[simp] lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n :=
  H.toPreLift.take_le_take (by omega) (by omega)
end Lift

variable (hyp) in
@[ext (flat := false)] structure WLLift extends Lift hyp where
  liftTree : Tree A
instance : Preorder (WLLift hyp) where
  le p q := p.toLift ≤ q.toLift
  le_refl _ := le_rfl (α := Lift hyp)
  le_trans _ _ _ := le_trans (α := Lift hyp)
namespace WLLift

variable (H : WLLift hyp)
def liftMediumVal : List A' := H.liftShort.val ++ [⟨H.liftNode, H.liftTree⟩]
@[simp, simp_lengths] lemma liftMediumVal_length :
  H.liftMediumVal.length (α := no_index _) = 2 * k + 2 := by simp [liftMediumVal]
@[simp] lemma getTree_liftMediumVal : getTree H.liftMediumVal = H.liftTree := by
  simp [liftMediumVal]
@[simp] lemma liftMediumVal_map : H.liftMediumVal.map Prod.fst = H.x.val.take (2 * k + 2) := by
  rw [liftMediumVal, List.map_append, H.liftShort_val_map, ← H.x.val.take_concat_get' (2 * k + 1)]
  dsimp [Lift.liftNode]

def liftVal := H.liftMediumVal ++
  (H.x.val.drop (2 * k + 2)).zipInitsMap (fun a y ↦ ⟨a, subAt H.liftTree y⟩)
@[simp] lemma liftVal_take_medium : H.liftVal.take (2 * k + 2) = H.liftMediumVal := by
  simp [liftVal]
@[simp] lemma liftVal_take_short : H.liftVal.take (2 * k + 1) = H.liftShort.val := by
  simp [liftVal, liftMediumVal]
@[simp] lemma liftVal_lift : H.liftVal.map Prod.fst = H.x.val := by
  simp [liftVal, ← List.zipInitsMap_map]
@[simp, simp_lengths] lemma liftVal_length : H.liftVal.length (α := no_index _)
  = H.x.val.length := by
  rw [← List.length_map, liftVal_lift]
@[simp] lemma liftVal_lift_get (h : n < H.liftVal.length) :
  H.liftVal[n].1 = H.x.val[n]'(by simpa using h) := by
  simp_rw [← liftVal_lift, List.getElem_map, upA]
lemma liftVal_take_eq_of_tree {H H' : WLLift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H.liftVal = H'.liftVal.take H.x.val.length := by
  simp [WLLift.liftVal]
  obtain ⟨n, hn⟩ := le_iff_exists_add.mp (by simp : H'.liftMediumVal.length ≤ H.x.val.length)
  rw [hn, List.take_append]; congr 1
  · simp_rw [liftMediumVal, ht]; rw [← Lift.eq_take_of_le h]; simp
  · rw [List.zipInitsMap_take, List.take_drop, ht, ← Lift.eq_take_of_le h]; simp [hn]
end WLLift

variable (hyp) in
structure WLLift' extends WLLift hyp where
  hlift : toWLLift.liftVal ∈ T'
namespace WLLift'
variable (H : WLLift' hyp)
@[simps coe] def lift : T' := ⟨H.liftVal, H.hlift⟩
attribute [simp_lengths] lift_coe
@[simp] lemma lift_lift : π H.lift = H.x := tree_ext H.liftVal_lift

section
variable (hp : IsPosition H.x.val Player.zero)
  (R : ResStrategy ⟨_, T'⟩ Player.zero H.x.val.length)
def extension := R H.lift (by synth_isPosition) (by simp)
def extensionMap := ExtensionsAt.map π H.lift_lift (H.extension hp R)
@[simp] lemma extension_take :
  (H.extension hp R).val' (A := no_index _).take (α := no_index _) (H.x.val.length (α := no_index _))
  = H.liftVal := by rw [ExtensionsAt.val'_take_of_eq _ (by simp)]; dsimp
@[simp] lemma extensionMap_take (h : n ≤ H.x.val.length) :
  (H.extensionMap hp R).val' (A := no_index _).take (α := no_index _) n
  = H.x.val.take n := by simpa [ExtensionsAt.val']
@[simp] lemma extension_take_medium :
  (H.extension hp R).val'.take (α := no_index _) (2 * k + 2) = H.liftMediumVal := by
  rw [ExtensionsAt.val'_take_of_le _ (by simp)]; simp [lift]
@[simps] def extensionPreLift : PreLift hyp where
  x := (H.extensionMap hp R).valT'
  R := H.R
  hlvl := by simp
@[simp] lemma extensionPreLift_take :
  (H.extensionPreLift hp R).take (H.x.val.length (α := no_index _)) (by simp) = H.toPreLift := by
  ext1 <;> simp [extensionPreLift, extensionMap, ← take_apply π]
@[simp] lemma extensionPreLift_liftShort : (H.extensionPreLift hp R).liftShort = H.liftShort := by
  rw [← extensionPreLift_take, PreLift.liftShort_take]
@[simp] lemma extensionPreLift_game : (H.extensionPreLift hp R).game = H.game := by
  ext <;> simp [PreLift.game_tree, PreLift.game_payoff]
@[simps! toPreLift] def extensionLift : Lift hyp where
  toPreLift := H.extensionPreLift hp R
  h'lvl := by simp
  conShort := by rw [← PreLift.conShort_iff_take, extensionPreLift_take]; exact H.conShort
@[simp] lemma extensionLift_take :
  (H.extensionLift hp R).take (H.x.val.length (α := no_index _)) (by simp) = H.toLift := by
  ext1; apply extensionPreLift_take
end
end WLLift'
end
end GaleStewartGame.BorelDet.Zero
