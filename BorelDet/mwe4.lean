import BorelDet.Proof.covering_closed_game
import BorelDet.Proof.win_asap

namespace GaleStewartGame.BorelDet.One
open InfList Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} [TopologicalSpace A] {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section

variable (hyp) in
@[ext] structure PreLift where
  x : T
  R : ResStrategy ⟨_, T'⟩ Player.one (2 * k + 1)
variable (hyp) in
@[ext (flat := false)] structure Lift extends PreLift hyp where
namespace Lift
variable (H : Lift hyp)

def Con := H.x.val.drop (2 * k + 1) = []
end Lift

variable (hyp) in
@[ext (flat := false)] structure Lift' extends Lift hyp where
  con : toLift.Con
namespace Lift'
variable (H : Lift' hyp)
@[simps] def lift : T' where
  val := have := H; sorry
  property := by sorry
@[simp] lemma lift_lift : π H.lift = H.x := sorry
attribute [simp_lengths] lift_coe
end Lift'

namespace PreLift
variable (H : PreLift hyp)
def extend := ({toPreLift := H} : Lift hyp)
def WonPos := have := H; {u : List A | sorry}
@[simps (config := {isSimp := false})] def game : Game A where
  tree := subAt T (H.x.val.take (2 * k + 1))
  payoff := Subtype.val⁻¹' ⋃ u ∈ H.WonPos, basicOpen u
def Won := ∃ u ∈ H.WonPos, u <+: H.x.val.drop (2 * k + 1)
def Winnable := WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
def Losable := ¬ WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
end PreLift

namespace Lift'
variable (H : Lift' hyp)
variable (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy ⟨_, T'⟩ Player.one H.x.val.length)
  (hR : R.res (by sorry) = H.R)
def extension := R H.lift (by have := hp; sorry) (by sorry)
def extensionMap := ExtensionsAt.map π H.lift_lift (H.extension hp R)
end Lift'
namespace PreLift
variable (hyp) in
structure LLift extends PreLift hyp where
  los : toPreLift.Losable
namespace LLift
variable (H : LLift hyp)
def toLift := H.extend
end LLift

variable (hyp) in
structure WLift extends PreLift hyp where
  won : toPreLift.Won
namespace WLift
variable (H : WLift hyp)
def toLift : Lift hyp := H.extend
end WLift

def Winnable.extension {H : PreLift hyp} (h : H.Winnable) : ExtensionsAt H.x := sorry

def extension (H : PreLift hyp) (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy ⟨_, T'⟩ Player.one H.x.val.length) : ExtensionsAt H.x :=
  if h : ∃ h : H.Won, (WLift.mk _ h).toLift.Con then (Lift'.mk _ h.2).extensionMap hp R
  else if h : H.Winnable then h.extension
  else if h : ∃ h : H.Losable, (LLift.mk _ h).toLift.Con then (Lift'.mk _ h.2).extensionMap hp R
  else choice (hyp.pruned H.x)

noncomputable def stratMap (lvl : ℕ) (R : ResStrategy ⟨_, T'⟩ Player.one lvl) :
  ResStrategy ⟨_, T⟩ Player.one lvl := fun x hp hlen ↦
  if _ : x.val.length ≤ 2 * k then (ResStrategy.fromMap π) (R.res hlen) x hp le_rfl
  else
    let pL : PreLift hyp := ⟨x, R.res (by sorry)⟩
    pL.extension hp (R.res hlen)
noncomputable def stratMap' (R : Strategy T' Player.one) : Strategy G.tree Player.one :=
  fun x hp ↦ stratMap x.val.length ((strategyEquivSystem R).str _) x hp le_rfl

structure TreeLift where
  R : Strategy T' Player.one
  --x : (stratMap' R).pre.subtree
