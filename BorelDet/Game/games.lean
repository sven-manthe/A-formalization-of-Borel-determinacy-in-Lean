import Mathlib.Data.Set.Subset
import BorelDet.Tree.tree_body
import BorelDet.Game.strategies

namespace GaleStewartGame
open Stream'.Discrete Descriptive Tree

variable {A : Type*} {p : Player}

/-- a Gale-Stewart game is given by a tree of valid plays (usually pruned) and a payoff set
  specifying the winner of an infinite play `a` : player 0 wins if and only if `a ∈ G.payoff` -/
@[ext 900] structure Game (A : Type*) where
  tree : tree A
  payoff : Set (body tree)
@[congr] lemma subtype_payoff {G G' : Game A} (h : G = G') :
  Subtype.val '' G.payoff = Subtype.val '' G'.payoff := by congr!
namespace Game
@[ext] lemma ext' {G G' : Game A} (ht : G.tree = G'.tree)
  (hp : Subtype.val '' G.payoff = Subtype.val '' G'.payoff) : G = G' := by
  ext1; exact ht; apply Set.hEq_of_image_eq _ hp; rw [ht]
/-- The residual game starting in position x -/
@[simps tree] def residual (G : Game A) (x : List A) : Game A where
  tree := subAt G.tree x
  payoff := (body.append x)⁻¹' if x.length % 2 = 0 then G.payoff else G.payoffᶜ
@[simp] lemma residual_payoff_even (G : Game A) (x : List A) (h : x.length % 2 = 0) :
  (G.residual x).payoff = (body.append x)⁻¹' G.payoff := by simp [residual, h]
@[simp] lemma residual_payoff_odd (G : Game A) (x : List A) (h : x.length % 2 = 1) :
  (G.residual x).payoff = ((body.append x)⁻¹' G.payoff)ᶜ := by simp [residual, h]
@[simp] lemma residual_nil (G : Game A) : G.residual [] = G := rfl
@[simp] lemma residual_append (G : Game A) (x y : List A) :
  (G.residual x).residual y = G.residual (x ++ y) := by
  ext1 <;> simp [residual]; split_ifs <;> simp <;> omega
lemma empty_of_tree (G : Game A) (h : G.tree = ⊥) : G = ⟨⊥, ∅⟩ := by
  ext1 <;> simp [Set.eq_empty_iff_forall_notMem, h]
lemma residual_notMem (G : Game A) (x : List A) (h : x ∉ G.tree) : G.residual x = ⟨⊥, ∅⟩ := by
  apply empty_of_tree; simpa
end Game

variable {G : Game A}
abbrev PreStrategy.subgame (S : PreStrategy G.tree p) : Game A where
  tree := S.subtree
  payoff := Subtype.val⁻¹' G.payoff

namespace Player
/-- player p wins if and only if the resulting play lies in `p.payoff G` -/
def payoff (p : Player) (G : Game A) : Set (body G.tree) := match p with
  | zero => G.payoff
  | one => G.payoffᶜ
@[simp] lemma payoff_zero : zero.payoff G = G.payoff := rfl
@[simp] lemma payoff_one : one.payoff G = G.payoffᶜ := rfl
@[simp] lemma payoff_swap : p.swap.payoff G = (p.payoff G)ᶜ := by cases p <;> simp
@[simp] lemma payoff_swap_residual {x : List A} :
  (p.swap.residual x).payoff G = ((p.residual x).payoff G)ᶜ := by
  rw [← p.residual_swap, payoff_swap]
@[simp] lemma payoff_residual x :
  p.payoff (G.residual x) = (body.append x)⁻¹' (p.residual x).payoff G := by
  by_cases h : x.length % 2 = 0 <;> cases p <;> simp_all
end Player
@[congr] lemma subtype_val_player_payoff {G' p'} (h : G = G') (hp : p = p') :
  Subtype.val '' (p.payoff G) = Subtype.val '' (p'.payoff G') := by congr!

/-- a PreStrategy is winning if all compatible plays are won -/
abbrev PreStrategy.IsWinning (s : PreStrategy G.tree p) := body s.subtree ⊆ p.payoff G
lemma PreStrategy.sub_winning {s t : PreStrategy G.tree p} (h : s ≤ t) (h' : t.IsWinning) :
  s.IsWinning := subset_trans (by gcongr) h'
lemma PreStrategy.IsWinning.residual {s : PreStrategy G.tree p} (h : s.IsWinning)
  (x : s.subtree) : (s.residual x).IsWinning (G := G.residual x) := by
  simpa [IsWinning] using Set.preimage_mono h
lemma PreStrategy.IsWinning.choose (s : QuasiStrategy G.tree p) (h : s.1.IsWinning) :
  s.2.choose.pre.IsWinning := PreStrategy.sub_winning (s.1.choose_sub s.2) h

namespace Game
@[congr] lemma exists_isWinning (S T : Game A) (p q : Player) (hS : S = T) (hp : p = q) :
  (∃ s : Strategy S.tree p, s.pre.IsWinning) ↔ ∃ s : Strategy T.tree q, s.pre.IsWinning := by
  subst hS hp; rfl
/-- whether a winning strategy exists for player p -/
def ExistsWinning (G : Game A) p := ∃ S : Strategy G.tree p, S.pre.IsWinning
lemma existsWinning_iff_quasi :
  G.ExistsWinning p ↔ ∃ S : QuasiStrategy G.tree p, S.1.IsWinning :=
  ⟨fun ⟨S, h'⟩ ↦ ⟨S.quasi, h'⟩, fun ⟨_, h'⟩ ↦ ⟨_, h'.choose⟩⟩
namespace ExistsWinning
variable (hW : G.ExistsWinning p)
include hW in lemma pruned (hW' : G.ExistsWinning p.swap) : IsPruned G.tree := by
  intro x; by_cases hp : IsPosition x.val p <;>
    [obtain ⟨S, _⟩ := hW; obtain ⟨S, _⟩ := hW'] <;> exact ⟨S x (by synth_isPosition)⟩
include hW in lemma not_both_winning (hNe : [] ∈ G.tree) : ¬ G.ExistsWinning p.swap := by
  intro hW'; have hP := hW.pruned hW'; rw [existsWinning_iff_quasi] at hW hW'
  obtain ⟨S, hS⟩ := hW; obtain ⟨S', hS'⟩ := hW'
  have h : body (S.1.subtree ⊓ S'.1.subtree) = ∅ := by
    cases p <;> simpa using Set.inter_subset_inter hS hS'
  let ⟨_, ha⟩ := ((S.restrict S'.1).subtree_isPruned
    (S'.subtree_isPruned hP)).body_ne_iff_ne.mpr
    ((S.restrict S'.1).1.subtree_ne.mpr (S'.1.subtree_ne.mpr hNe))
  exact h.subset (by simpa using ha)
end ExistsWinning
def AllWinning (G : Game A) (p : Player) := p.payoff G = Set.univ
lemma AllWinning.residual (hW : G.AllWinning p) x :
  (G.residual x).AllWinning (p.residual x) := by simp_all [AllWinning]
/-- a game is determined if some player has a winning strategy -/
def IsDetermined (G : Game A) := ∃ p, G.ExistsWinning p
end Game

end GaleStewartGame
