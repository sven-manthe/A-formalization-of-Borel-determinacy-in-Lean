import BorelDet.Applications.Meager
import BorelDet.Proof.borel_determinacy

open GaleStewartGame
open Descriptive

variable {X : Type*} (V : Set (Set X)) (PO : Set (Set X))
def chainTree : tree V where
    val := {x | x.IsChain (· ≥ ·)}
    property _ _ := List.IsChain.left_of_append
lemma def_chainTree (x : List V) : x ∈ chainTree V ↔ x.IsChain (· ≥ ·) := by
    simp [chainTree]
lemma nil_mem_chainTree : [] ∈ chainTree V := by simp [chainTree]
lemma concat_mem_chainTree {x A} :
    x ++ [A] ∈ chainTree V ↔ x ∈ chainTree V ∧ ∀ hx, A ≤ x.getLast hx := by
    simp_rw [def_chainTree, List.isChain_append, List.isChain_singleton]
    obtain rfl | ⟨x, ⟨B, rfl⟩⟩ := x.eq_nil_or_concat' <;> simp
def chainTree.concat (x : chainTree V) (A : V) (h : ∀ hx, A ≤ x.val.getLast hx) : chainTree V where
    val := x.val ++ [A]
    property := by rw [concat_mem_chainTree]; use x.prop
--TODO win conjunctions by combining strategies
def interGame : Game V where
    tree := chainTree V
    payoff A := PO (⋂ n, A.1 n)
variable {V}
variable {W : Set (Set X)} (hWV : W ⊆ V) (hW : ∀ A ∈ V, ∃ B ∈ W, B ⊆ A)
lemma extend_mem_iff (x : List W) : x.map (Set.inclusion hWV) ∈ chainTree V ↔ x ∈ chainTree W := by
    simp [chainTree, List.isChain_map]
@[simps] def extend (x : chainTree W) : chainTree V where
    val := x.1.map (Set.inclusion hWV)
    property := by simpa only [extend_mem_iff] using x.2
@[simps] def extend' {x : chainTree W} (a : Tree.ExtensionsAt x) :
    Tree.ExtensionsAt (extend hWV x) where
    val := Set.inclusion hWV a.val
    property := by
        rw [← List.map_singleton, extend_coe, ← List.map_append, extend_mem_iff]
        exact a.prop
def choose_pair (A : V) : W where
    val := (hW A A.coe_prop).choose
    property := (hW A A.coe_prop).choose_spec.1
lemma choose_pair_sub A : (choose_pair hW A).val ⊆ A.val := (hW A A.coe_prop).choose_spec.2
def shrink' {x : chainTree W} (a : Tree.ExtensionsAt (extend hWV x)) :
    Tree.ExtensionsAt x := ⟨_, (chainTree.concat W x (choose_pair hW a.val) (by
        intro _; apply (choose_pair_sub hW a.val).trans
        have ha := a.prop; rw [concat_mem_chainTree] at ha
        simpa using ha.2 (by simpa))).prop⟩
attribute [simp_lengths] extend_coe

section restrict
variable {p : Player} (S : Strategy (chainTree V) p)
--TODO cases fails in synth_isPosition if target depends?
def restrict : Strategy (chainTree W) p := fun x hp ↦
    shrink' hWV hW (S (extend hWV x) (by synth_isPosition))
--TODO eigene Züge wie mit alter Strategie, choose vor Zügen des Gegners
def restrict_tree (x : S.pre.subtree) : (restrict hWV hW S).pre.subtree :=
    List.reverseRecOn x.val ⟨[], by simp [nil_mem_chainTree]⟩ fun xs A ys ↦ --TODO need to distingush parity
        ⟨chainTree.concat W (PreStrategy.subtree_incl _ ys) (choose_pair hW A) (by
        simp
        have : xs ++ [A] ∈ S.pre.subtree := by sorry --TODO need tree reverseRecOn here´
        have h := this.1
        rw [concat_mem_chainTree] at h
        intro _; apply (choose_pair_sub hW A).trans
        --TODO need ys restrict to xs here
        sorry), sorry⟩
lemma restrict_winning (h : S.pre.IsWinning (G := interGame V PO)) :
    (restrict hWV hW S).pre.IsWinning (G := interGame W PO) := by
    sorry --TODO restrict body sub
end restrict

namespace Choquet
variable (X)
variable [TopologicalSpace X]
def game := interGame (X := X) {A | IsOpen A ∧ A.Nonempty} {∅}
def IsChoquet := (game X).ExistsWinning Player.one
end Choquet
--TODO: here Banach-Mazur games could be added
