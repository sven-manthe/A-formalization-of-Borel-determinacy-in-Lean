import BorelDet.Basic.general

namespace GaleStewartGame

inductive Player
  | zero
  | one

section
open Lean Meta Elab Tactic Term Qq
elab "casesPlayer" : tactic => withMainContext do
  for hyp in ← getLCtx do
    if ← isDefEq (← instantiateMVars hyp.type) q(Player) then
      let syn ← exprToSyntax hyp.toExpr
      evalTactic (← `(tactic | cases $syn:term))
      return
  throwError "no variable of type player"
macro "casesPlayers" : tactic => `(tactic | focus repeat all_goals casesPlayer)
attribute [simp_isPosition]
  iff_true iff_false true_iff false_iff
  and_true true_and and_false false_and
  or_true true_or or_false false_or

  ite_eq_iff eq_ite_iff ite_prop_iff_or
  --apply_ite
  --maybe reduce priority to stop (apply_ite (Eq _))
attribute [simp_isPosition] reduceCtorEq
macro "synth_isPosition" : tactic =>
  `(tactic | first | done |
  (casesPlayers <;> (try apply_fun List.length at *) <;>
    simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition, simp_lengths] <;>
    /-(try split_ifs at * <;> --split_ifs at * fails in win_asap due to order issue (manually reordering goals fixes the issue)
      simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition]) <;>-/
    omega))
end

variable {A : Type*} (x : List A) (p q : Player)
namespace Player
def toNat : Player → ℕ
  | zero => 0
  | one => 1
@[simp_isPosition] def apply_ite_toNat := apply_ite toNat
@[simp, simp_isPosition] lemma zero_toNat : zero.toNat = 0 := rfl
@[simp, simp_isPosition] lemma one_toNat : one.toNat = 1 := rfl
@[ext] lemma ext (h : p.toNat = q.toNat) : p = q := by synth_isPosition

def swap : Player → Player
  | zero => one
  | one => zero
@[simp_isPosition] def apply_ite_swap := apply_ite swap
@[simp, simp_isPosition] theorem swap_zero : zero.swap = one := rfl
@[simp, simp_isPosition] theorem swap_one : one.swap = zero := rfl

@[simp_isPosition] def residual := if x.length % 2 = 0 then p else p.swap
end Player

@[simp_isPosition] def IsPosition (x : List A) (p : Player) : Prop := x.length % 2 = p.toNat



namespace Player
@[simp] theorem residual_swap :
  (p.residual x).swap = p.swap.residual x := by synth_isPosition
@[simp] lemma residual_residual {x y : List A} :
  (p.residual x).residual y = p.residual (x ++ y) := by synth_isPosition
@[simp] theorem residual_even (h : x.length % 2 = 0) :
  p.residual x = p := by synth_isPosition
@[simp] theorem residual_odd (h : x.length % 2 = 1) :
  p.residual x = p.swap := by synth_isPosition
@[simp] lemma residual_append_both {y} : (p.residual (x ++ (y ++ x))) = p.residual y := by
  synth_isPosition
@[simp] lemma residual_cons {a} : (p.residual (a :: x)) = (p.residual x).swap := by
  synth_isPosition
@[simp] lemma residual_append_cons {a} {y} :
  (p.residual (x ++ a :: y)) = (p.residual (x ++ y)).swap := by synth_isPosition
@[simp] lemma residual_concat {a} : (p.residual (x ++ [a])) = (p.residual x).swap := by
  synth_isPosition
@[simp] lemma residual_concat2 {a b} : (p.residual (x ++ [a, b])) = p.residual x := by
  synth_isPosition
end Player
/-this should probably be removed
namespace Player
@[simp] lemma zero_toNat_iff : p.toNat = 0 ↔ p = zero := by synth_isPosition
@[simp] lemma zero_toNat_iff' : 0 = p.toNat ↔ p = zero := by synth_isPosition
@[simp] lemma one_toNat_iff : p.toNat = 1 ↔ p = one := by synth_isPosition
@[simp] lemma one_toNat_iff' : 1 = p.toNat ↔ p = one := by synth_isPosition

@[simp] theorem equal_swap_ne : p ≠ q ↔ p = q.swap := by
  cases p <;> cases q <;> tauto
@[simp] theorem swap_rhs : p.swap = q ↔ p = q.swap := by
  cases p <;> cases q <;> tauto
@[simp] theorem swap_swap : p.swap.swap = p := by cases p <;> rfl
@[simp] lemma swap_toNat : p.swap.toNat = 1 - p.toNat := by synth_isPosition

@[simp] theorem residual_even (h : x.length % 2 = 0) :
  p.residual x = p := by synth_isPosition
@[simp] theorem residual_odd (h : x.length % 2 = 1) :
  p.residual x = p.swap := by synth_isPosition
@[simp] lemma residual_residual {x y : List A} :
  (p.residual x).residual y = p.residual (x ++ y) := by synth_isPosition
@[simp] lemma residual_toNat : (p.residual x).toNat = (p.toNat + x.length) % 2 := by
  synth_isPosition
@[simp] theorem residual_swap :
  (p.residual x).swap = p.swap.residual x := by synth_isPosition
@[simp] lemma residual_cons {a} : (p.residual (a :: x)) = (p.residual x).swap := by
  synth_isPosition
@[simp] lemma residual_concat {a} : (p.residual (x ++ [a])) = (p.residual x).swap := by
  synth_isPosition
@[simp] lemma residual_concat2 {a b} : (p.residual (x ++ [a, b])) = p.residual x := by
  synth_isPosition
@[simp] lemma residual_append_both {y} : (p.residual (x ++ (y ++ x))) = p.residual y := by
  synth_isPosition
end Player
namespace IsPosition
theorem append_left {x y : List A} :
  IsPosition (x ++ y) p ↔ (x.length % 2 = 0 ↔ IsPosition y p) := by synth_isPosition
theorem append_right {x y : List A} :
  IsPosition (x ++ y) p ↔ (y.length % 2 = 0 ↔ IsPosition x p) := by synth_isPosition
@[simp] lemma append_both {x y : List A} :
  IsPosition (x ++ (y ++ x)) p ↔ IsPosition y p := by synth_isPosition
@[simp] theorem even {p : Player} {x : List A} (h : x.length % 2 = 0) :
  IsPosition x p ↔ p = Player.zero := by synth_isPosition
@[simp] theorem odd {p : Player} {x : List A} (h : x.length % 2 = 1) :
  IsPosition x p ↔ p = Player.one := by synth_isPosition
@[simp] theorem not {x : List A} {p : Player} :
  ¬ IsPosition x p ↔ IsPosition x p.swap := by synth_isPosition
@[simp] theorem change {x : List A} {a : A} {p : Player} :
  IsPosition (x ++ [a]) p ↔ IsPosition x p.swap := by synth_isPosition
@[simp] theorem change2 {x : List A} {a b : A} {p : Player} :
  IsPosition (x ++ [a, b]) p ↔ IsPosition x p := by synth_isPosition
@[simp] theorem cons {x : List A} {a : A} {p : Player} :
  IsPosition (a :: x) p ↔ IsPosition x p.swap := by synth_isPosition
@[simp] theorem residual {x y : List A}  {p : Player} :
  IsPosition y (p.residual x) ↔ IsPosition (x ++ y) p := by synth_isPosition
end IsPosition-/

end GaleStewartGame
