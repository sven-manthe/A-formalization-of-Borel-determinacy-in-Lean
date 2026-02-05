import BorelDet.Proof.Zero.pre_lift

namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section
variable (H : Lift hyp)
namespace Lift
def liftShortWinStrat :
  QuasiStrategy (subAt H.game.tree [H.liftNode]) Player.one :=
  defensiveQuasi (H.game.residual [H.liftNode]) Player.one (H.game_pruned.sub _)
@[simps toLift] def toWLift : WLLift hyp where
  toLift := H
  liftTree := (liftShortWinStrat H).1.subtree
attribute [simp_lengths] toWLift_toLift
@[simp] lemma liftTree_take n h : (H.take n h).toWLift.liftTree = H.toWLift.liftTree := by
  simp [toWLift, liftShortWinStrat, liftShortWinStrat]; congr! 2 <;> simp --TODO congr and simp use wrong congruence lemma, but congr! use provided one
@[simp] lemma liftMediumVal_take n h :
  (H.take n h).toWLift.liftMediumVal = H.toWLift.liftMediumVal := by simp [WLLift.liftMediumVal]
@[simp] lemma liftVal_take n h : (H.take n h).toWLift.liftVal = H.toWLift.liftVal.take n := by
  by_cases H.x.val.length ≤ n
  · rw [Lift.take_of_length_le, List.take_of_length_le] <;> simp [*]
  · convert WLLift.liftVal_take_eq_of_tree _ _
    · simp; omega
    · apply Lift.take_le; exact h
    · simp
lemma wLift_liftVal_mono {H H' : Lift hyp} (h : H ≤ H') :
  H.toWLift.liftVal <+: H'.toWLift.liftVal := by
  rw [List.prefix_iff_eq_take, ← H'.liftVal_take _  (by simp)]
  simp_rw [WLLift.liftVal_length, toWLift_toLift]; congr; ext1; exact h.symm
namespace Winnable
variable (hW : H.Winnable)
variable {H}
include hW in lemma take n h : (H.take n h).Winnable := by
  intro ⟨m, hm⟩; apply hW; use min (2 * k + 1 + m) n - (2 * k + 1)
  have : 2 * k + 1 + (min (2 * k + 1 + m) n - (2 * k + 1)) = min (2 * k + 1 + m) n := by omega
  simpa only [List.take_drop, this, Lift.take_toPreLift, PreLift.game_take,
    PreLift.take_x, take_coe, List.take_take] using hm
include hW in lemma liftMedium_mem : H.toWLift.liftMediumVal ∈ T' := by
  dsimp [WLLift.liftMediumVal, Lift.liftNode]
  simp_rw [gameTree_concat]; use (H.R _ _ _).prop
  constructor
  · simp_rw (config := {singlePass := true}) [
      ← add_zero (2 * k + 1), List.getElem_drop', List.getElem_zero]
    exact mem_of_prefix ⟨(H.x.val.drop (2 * k + 1)).tail, by simp⟩ hW.conLong --TODO diagnostics: this unfolds constTreeObj?
  · simp; right; rw [WinningCondition.concat]; refine ⟨?_, H.liftShortWinStrat, rfl⟩
    have h := (H.game.residual [H.liftNode]).gale_stewart_precise'
      (by simpa using H.game_closed.preimage (body.append_con _)) (H.game_pruned.sub _)
      (by
        intro hS; apply hW; use 1
        have hxlt : 2 * k + 1 < H.x.val.length :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) H.h'lvl
        have : (H.x.val.drop (2 * k + 1)).take 1 = [H.liftNode] := by
          simpa [Lift.liftNode] using (List.take_one_drop_eq_of_lt_length (l := H.x.val) (n := 2 * k + 1) hxlt)
        simpa only [this] using hS)
    simp_rw [pullSub_body, Set.image_subset_iff]
    apply subset_trans h
    intro a ha
    -- Unfolding `H.game.payoff` produces a goal about the original game's payoff; handle it explicitly.
    simp [PreLift.game_payoff] at ha ⊢
    rcases ha with ⟨⟨hGT, hHgT⟩, hnot⟩
    -- Use the residual-payoff characterization (odd prefix length) to turn `hnot` into a payoff proof.
    have hodd : (List.take (2 * k + 1) H.x.val).length % 2 = 1 := by
      have hlen : (List.take (2 * k + 1) H.x.val).length = 2 * k + 1 := by
        simp [List.length_take, Nat.min_eq_left (le_trans (Nat.le_succ _) H.h'lvl)]
      have h0 : (2 * k) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 k)
      have h' : (2 * k + 1) % 2 = 1 := by
        calc
          (2 * k + 1) % 2 = ((2 * k) % 2 + 1 % 2) % 2 := by simp [Nat.add_mod]
          _ = (0 + 1) % 2 := by simp [h0]
          _ = 1 := by simp
      simp [hlen]
    refine ⟨?_, ?_⟩
    · -- body membership for the full stream
      simpa [Lift.liftNode, ← Stream'.append_eq_cons, ← Stream'.append_append_stream] using hGT
    · -- payoff membership for the full stream
      have hnot' := hnot hHgT hGT
      have hx :
          List.take (2 * k + 1) H.x.val ++ₛ Stream'.cons H.liftNode a ∈ Subtype.val '' G.payoff := by
        have hsub :
            Stream'.cons H.liftNode a ∈ body (subAt G.tree (List.take (2 * k + 1) H.x.val)) := by
          simpa [Tree.subAt_body] using hGT
        have :
            (⟨Stream'.cons H.liftNode a, hsub⟩ : body (subAt G.tree (List.take (2 * k + 1) H.x.val)))
              ∉ (G.residual (List.take (2 * k + 1) H.x.val)).payoff := by
          simpa using hnot'
        have :
            (⟨Stream'.cons H.liftNode a, hsub⟩ : body (subAt G.tree (List.take (2 * k + 1) H.x.val)))
              ∈ (body.append (List.take (2 * k + 1) H.x.val))⁻¹' G.payoff := by
          simpa [Game.residual_payoff_odd _ _ hodd] using this
        exact (mem_subAt_body (X := G.payoff) (x := List.take (2 * k + 1) H.x.val)
          (y := (⟨Stream'.cons H.liftNode a, hsub⟩))).1 this
      have hxEq' :
          (List.take (2 * k + 1 + 1) H.x.val ++ₛ a) =
            (List.take (2 * k + 1) H.x.val ++ₛ Stream'.cons H.liftNode a) := by
        simp [Lift.liftNode, ← Stream'.append_eq_cons, ← Stream'.append_append_stream]
      have hx' : List.take (2 * k + 1 + 1) H.x.val ++ₛ a ∈ Subtype.val '' G.payoff := by
        simpa [hxEq'] using hx
      rcases hx' with ⟨x', hx'P, hx'Eq⟩
      have hx'body :
          (⟨List.take (2 * k + 1 + 1) H.x.val ++ₛ a,
              by simpa [hxEq'] using hGT⟩ : body G.tree) = x' := by
        ext1
        simpa using hx'Eq.symm
      simpa [hx'body] using hx'P
@[simps toWLLift] def toWLift' : WLLift' hyp where
  toWLLift := H.toWLift
  hlift := by
    let ⟨n, hn⟩ := le_iff_exists_add.mp H.h'lvl
    induction' n with n ih generalizing H
    · rw [WLLift.liftVal, List.drop_of_length_le (by simp [hn])]; simpa using hW.liftMedium_mem
    · specialize ih (hW.take (2 * k + 2 + n) (by omega)); simp [hn] at ih
      rw [H.toWLift.liftVal.eq_take_concat (2 * k + 2 + n) (by simpa)]
      simp [- List.take_append_getElem]; use ih; constructor
      · rw [getTree_eq' _ ih, List.map_drop, ← H.liftVal_take _ (by omega), WLLift.liftVal_lift,
          mem_subAt, toWLift_toLift, take_toPreLift, PreLift.take_x, take_coe, ← List.take_drop,
          List.getElem_drop', List.take_concat_get', List.take_drop, ← hn]
        simp [toWLift]
        apply WinningPrefix.mem_defensiveQuasi ⟨_, by simpa [Lift.liftNode] using hW.conLong⟩
        intro hwin; apply hW
        simpa [Lift.liftNode] using hwin.winningPrefix_of_residual
      · conv => lhs; unfold WLLift.liftVal; rw [List.getElem_append_right (by simp)]
        rw [getTree_eq' _ ih]; simp [List.drop_take]; congr
        · simp [List.take_take, WLLift.liftVal]
        · rw [List.getElem_drop', List.take_concat_get']
attribute [simp_lengths] toWLift'_toWLLift
/-lemma extracted_1 {H : WLLift' hyp} (hp) (R) (h') :
  (ExtensionsAt.val' (ExtensionsAt.map π (x := H.lift)
    (y := @PreLift.x A inferInstance G k hyp H.toPreLift) h' (H.extension hp R))) =
    ... := by
    rw [ExtensionsAt.map_val'] --adding π fixes-/
lemma extension_conLong hp R : (hW.toWLift'.extensionLift hp R).ConLong := by
  have hm : H.x.val[2 * k + 1] :: (((hW.toWLift'.extensionMap hp R).val').drop (2 * k + 2))
    ∈ H.game.tree := by
    have hm' := by simpa using (mem_getTree (hW.toWLift'.extension hp R).valT').2
    rw [ExtensionsAt.val'_take_of_le _ (by simp)] at hm'; simp [toWLift] at hm'
    have hmin : min (2 * k + 2) (H.x.val.length + 1) = 2 * k + 2 := by
      apply Nat.min_eq_left
      have hxle : 2 * k + 2 ≤ H.x.val.length := H.h'lvl
      exact hxle.trans (Nat.le_succ _)
    simpa [hmin, liftNode, WLLift'.extensionMap, ExtensionsAt.map_val' π] using hm'.1
  simp [PreLift.ConLong]; convert hm using 1
  have hxlt' : 2 * k + 1 < H.x.val.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) H.h'lvl
  have hxlt : 2 * k + 1 < (hW.toWLift'.extensionMap hp R).val'.length := by
    -- `extensionMap` extends `H.x` by one element.
    simpa [WLLift'.extensionMap, ExtensionsAt.map_val', ExtensionsAt.val', ExtensionsAt.val'_length] using
      Nat.lt_succ_of_lt hxlt'
  -- Rewrite the dropped prefix of the extension into `head :: tail`.
  rw [← List.getElem_cons_drop (as := (hW.toWLift'.extensionMap hp R).val') (i := 2 * k + 1) hxlt]
  congr 1
  -- The first `2*k+2` elements of the extension coincide with `H.x`.
  simp [WLLift'.extensionMap, ExtensionsAt.val', hxlt']
end Winnable

variable (hyp) in
@[ext (flat := false)] structure LLift extends Lift hyp where
  lost' : toLift.Lost'
namespace LLift
variable (H : LLift hyp)
lemma losable (h : H.ConLong) : H.Losable := by
  use h; use H.x.val.length - (2 * k + 1); rw [List.take_of_length_le (by simp)]
  apply AllWinning.existsWinning _ (H.game_pruned.sub _); have hL := H.lost'
  simp [Lost', WonPosition, AllWinning] at hL ⊢
  rw [Set.eq_empty_iff_forall_notMem] at *; rintro ⟨x, hx⟩ ⟨hx', hxp⟩
  simp at hx hxp; apply hL ⟨x, by
    simpa [← Stream'.append_append_stream] using body_mono H.game_tree_sub hx⟩
  -- Turn the residual non-payoff into a payoff statement, then transport along the stream equality.
  have hodd : (List.take (2 * k + 1) H.x.val).length % 2 = 1 := by
    have hlen : (List.take (2 * k + 1) H.x.val).length = 2 * k + 1 := by
      simp [List.length_take, Nat.min_eq_left (le_trans (Nat.le_succ _) H.h'lvl)]
    have h0 : (2 * k) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 k)
    have h' : (2 * k + 1) % 2 = 1 := by
      calc
        (2 * k + 1) % 2 = ((2 * k) % 2 + 1 % 2) % 2 := by simp [Nat.add_mod]
        _ = (0 + 1) % 2 := by simp [h0]
        _ = 1 := by simp
    simp [hlen]
  have hxmem : hx' ∈ (body.append (List.take (2 * k + 1) H.x.val))⁻¹' G.payoff := by
    have : hx' ∈ (G.residual (List.take (2 * k + 1) H.x.val)).payoffᶜ := by
      simpa using hxp.1
    simpa [Game.residual_payoff_odd _ _ hodd] using this
  have hximage : List.take (2 * k + 1) H.x.val ++ₛ hx'.val ∈ Subtype.val '' G.payoff :=
    (mem_subAt_body (X := G.payoff) (x := List.take (2 * k + 1) H.x.val) (y := hx')).1 hxmem
  have hximage' : H.x.val ++ₛ x ∈ Subtype.val '' G.payoff := by
    -- use the stored equality to align prefixes
    simpa [← Stream'.append_append_stream, List.take_append_drop, hxp.2] using hximage
  have hxbody : x ∈ body (subAt G.tree H.x.val) := by
    -- `hximage'` witnesses a payoff stream, hence a body stream
    rcases hximage' with ⟨y, hyP, hyEq⟩
    have : H.x.val ++ₛ x ∈ body G.tree := by simpa [hyEq] using y.prop
    simpa [subAt_body] using this
  exact (mem_subAt_body (X := G.payoff) (x := H.x.val) (y := ⟨x, hxbody⟩)).2 hximage'
lemma exists_prefix : ∃ n h, (H.take n h).Lost' :=
  ⟨H.x.val.length, H.h'lvl, by simpa using H.lost'⟩
def minLength := Nat.find H.exists_prefix
@[simp] lemma minLength_le : H.minLength ≤ H.x.val.length (α := no_index _) :=
  Nat.find_le ⟨H.h'lvl, by simpa using H.lost'⟩
@[simp] lemma le_minLength : 2 * k + 2 ≤ H.minLength := (Nat.find_spec H.exists_prefix).1
@[simps!] def takeMin := H.take H.minLength H.le_minLength
@[simp] lemma takeMin_liftShort : H.takeMin.liftShort = H.liftShort := by
  simp [takeMin]
@[simp] lemma takeMin_game : H.takeMin.game = H.game := by simp [takeMin]
lemma min_prefix : H.takeMin.Lost' := (Nat.find_spec H.exists_prefix).2
lemma le_of_take {n : ℕ} {h : 2 * k + 2 ≤ n} (hL : (H.take n h).Lost') :
  H.minLength ≤ n := by simpa using Nat.find_le ⟨h, by simpa⟩
@[simps toLift] def toWLLift : WLLift hyp where
  toLift := H.toLift
  liftTree := pullSub (subAt G.tree H.takeMin.x.val) (H.takeMin.x.val.drop (2 * k + 2))
end LLift
@[simps toLift] def Lost'.mk {H : Lift hyp} (h : Lost' H) : LLift hyp := LLift.mk _ h
attribute [simp_lengths] LLift.toWLLift_toLift Lost'.mk_toLift

section extend'
variable {H}
variable {h} (hL : (H.take n h).Lost')
@[simps toLift] def extend' : LLift hyp where
  toLift := H
  lost' := by simpa using WonPosition.extend (H.x.val.drop n) hL
lemma extend'_le : (H.extend' hL).minLength ≤ n := (H.extend' hL).le_of_take hL
@[simp] lemma minLength_extend' : (H.extend' hL).minLength = hL.mk.minLength := by
  apply le_antisymm
  · exact Nat.find_mono fun m ⟨hm, hl⟩ ↦
      ⟨hm, (extend' (by simpa [min_comm] using hl : ((H.take m hm).take n h).Lost')).lost'⟩
  · apply Nat.find_le; simp; convert (H.extend' hL).min_prefix
    simp [LLift.takeMin]; congr; simpa using extend'_le hL
lemma extend'_le' : hL.mk.minLength ≤ n := by simpa using extend'_le hL
@[simp] lemma takeMin_extend' : (H.extend' hL).takeMin = hL.mk.takeMin := by
  simp [LLift.takeMin]; congr; simpa using extend'_le hL
@[simp] lemma liftTree_extend' :
  (H.extend' hL).toWLLift.liftTree = hL.mk.toWLLift.liftTree := by
  simp [LLift.toWLLift, List.take_take, extend'_le' hL]
@[simp] lemma liftMediumVal_extend' :
  (H.extend' hL).toWLLift.liftMediumVal = hL.mk.toWLLift.liftMediumVal := by
  simp [WLLift.liftMediumVal]
@[simp] lemma liftVal_extend' :
  (H.extend' hL).toWLLift.liftVal.take n = hL.mk.toWLLift.liftVal := by
  by_cases H.x.val.length ≤ n
  · rw [List.take_of_length_le]; congr 2; ext1; simp; rw [Lift.take_of_length_le]
    all_goals simpa
  · symm; convert WLLift.liftVal_take_eq_of_tree _ _
    · simp; omega
    · apply Lift.take_le; exact h
    · simp
end extend'

lemma lost'_of_le {H H' : Lift hyp} (h : H.Lost') (h' : H ≤ H') : H'.Lost' := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h
  exact (H'.extend' h).lost'
lemma lLift_liftVal_mono {H H' : Lift hyp} (h : H.Lost') (h' : H ≤ H') :
  h.mk.toWLLift.liftVal <+: (lost'_of_le h h').mk.toWLLift.liftVal := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h ⊢
  show h.mk.toWLLift.liftVal <+: _; rw [← liftVal_extend']; apply List.take_prefix
def Lost := ∃ (h : Lost' H), h.mk.takeMin.ConLong
namespace Lost
variable (hL : H.Lost)
variable {H}
lemma extend {h} (hL : (H.take n h).Lost) : H.Lost := by
  use (H.extend' hL.1).lost'; show (H.extend' hL.1).takeMin.ConLong; simpa using hL.2
lemma lost_of_le {H H' : Lift hyp} (h : H.Lost) (h' : H ≤ H') : H'.Lost := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h; exact h.extend
lemma liftMedium_mem : hL.1.mk.toWLLift.liftMediumVal ∈ T' := by
  dsimp [WLLift.liftMediumVal, Lift.liftNode, gameAsTrees]
  simp_rw [gameTree_concat]; use SetLike.coe_mem _; constructor
  · simp_rw (config := {singlePass := true}) [← add_zero (2 * k + 1),
      List.getElem_drop', List.getElem_zero]
    simpa using mem_of_prefix ⟨(hL.1.mk.takeMin.x.val.drop (2 * k + 1)).tail, by
      have hlenH : 2 * k + 1 < H.x.val.length := by
        exact lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) H.h'lvl
      have hlenMin : 2 * k + 1 < hL.1.mk.minLength := by
        exact lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) hL.1.mk.le_minLength
      have htake : 2 * k + 1 < (List.take hL.1.mk.minLength H.x.val).length := by
        simpa [List.length_take, Nat.lt_min] using And.intro hlenMin hlenH
      simpa [List.tail_drop] using
        (List.drop_eq_getElem_cons (l := List.take hL.1.mk.minLength H.x.val)
          (i := 2 * k + 1) htake).symm⟩ hL.2
  · simp; left; rw [LosingCondition.concat]
    refine ⟨?_, ⟨hL.1.mk.takeMin.x.val.drop (2 * k + 2), ?_⟩, ?_⟩
    · simp [LLift.toWLLift]; rw [← Set.subset_empty_iff]
      rintro _ ⟨⟨z, hzb, hze⟩, ⟨_, _, rfl⟩⟩
      apply (wonPosition_iff_disjoint'.mp hL.1.mk.min_prefix).subset ⟨_, by simpa⟩
      use ⟨z, by simpa⟩; ext1
      simp [← Stream'.append_append_stream] at hze
      rw [List.drop_take, ← List.take_add] at hze
      have hlen : 2 * k + 2 + (hL.1.mk.minLength - (2 * k + 2)) = hL.1.mk.minLength := by
        exact Nat.add_sub_of_le hL.1.mk.le_minLength
      -- rewrite `2*k+1+1` into `2*k+2` and close with `hlen`
      have hidx :
          1 + (1 + (2 * k + (hL.1.mk.minLength - (2 + 2 * k)))) =
            2 * k + 2 + (hL.1.mk.minLength - (2 * k + 2)) := by
        omega
      simpa [hidx, hlen] using hze
    · rw [LLift.takeMin_x_coe]; simp
      have hlenH : 2 * k + 1 < H.x.val.length := by
        exact lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) H.h'lvl
      have hlenMin : 2 * k + 1 < hL.1.mk.minLength := by
        exact lt_of_lt_of_le (Nat.lt_succ_self (2 * k + 1)) hL.1.mk.le_minLength
      have htake : 2 * k + 1 < (List.take hL.1.mk.minLength H.x.val).length := by
        simpa [List.length_take, Nat.lt_min] using And.intro hlenMin hlenH
      rw [List.getElem_take' (xs := H.x.val) (i := 2 * k + 1) (j := hL.1.mk.minLength)
        (hi := hlenH) (hj := hlenMin)]
      rw [← List.drop_eq_getElem_cons (l := List.take hL.1.mk.minLength H.x.val)
        (i := 2 * k + 1) htake]
      simpa [PreLift.ConLong] using hL.2
    · simp [LLift.toWLLift]
      rw [List.append_cons, List.take_concat_get', List.drop_take, ← List.take_add]
      have hidx :
          2 * k + 1 + 1 + (hL.1.mk.minLength - (2 * k + 2)) = hL.1.mk.minLength := by
        have hlen : 2 * k + 2 + (hL.1.mk.minLength - (2 * k + 2)) = hL.1.mk.minLength := by
          exact Nat.add_sub_of_le hL.1.mk.le_minLength
        calc
          2 * k + 1 + 1 + (hL.1.mk.minLength - (2 * k + 2)) =
              2 * k + 2 + (hL.1.mk.minLength - (2 * k + 2)) := by
                omega
          _ = hL.1.mk.minLength := hlen
      simp [hidx]
lemma lift_mem n : hL.1.mk.toWLLift.liftMediumVal ++
  ((H.x.val.drop (2 * k + 2)).take n).zipInitsMap
  (fun a y ↦ ⟨a, subAt hL.1.mk.toWLLift.liftTree y⟩) ∈ T' := by
  induction' n with n ih
  · simpa using hL.liftMedium_mem
  · simp only [List.take_add_one, List.zipInitsMap_append, List.getElem?_drop] at ih ⊢
    by_cases hn : 2 * k + 2 + n ≥ H.x.val.length
    · erw [List.getElem?_eq_none_iff.mpr hn]
      simpa only [Option.toList_none, List.zipInitsMap_nil, List.append_nil] using ih
    · rw [List.getElem?_eq_getElem (by as_aux_lemma => omega)]; simp [← List.append_assoc]
      use ih; rw [getTree_eq' _ ih]
      refine ⟨?_, by simp [← List.zipInitsMap_map]⟩
      rw [List.take_left' (WLLift.liftMediumVal_length _)]
      simp only [LLift.toWLLift,
        WLLift.getTree_liftMediumVal, WLLift.liftMediumVal_length, List.drop_left', mem_subAt]
      by_cases hn : 2 * k + 2 + n + 1 ≤ hL.1.mk.minLength
      ·
        have hn' : n + 1 ≤ hL.1.mk.minLength - (2 * k + 2) := by
          omega
        have hmin_le : hL.1.mk.minLength ≤ H.x.val.length := hL.1.mk.minLength_le
        have hlen_map :
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y)))).length ≤ n := by
          calc
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y)))).length
                = (List.take n (List.drop (2 * k + 2) H.x.val)).length := by
                  simp [List.zipInitsMap_length]
            _ = min n (H.x.val.drop (2 * k + 2)).length := by simp [List.length_take]
            _ ≤ n := Nat.min_le_left _ _
        have hylen :
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y))) ++
              [H.x.val[2 * k + 2 + n]]).length ≤ n + 1 := by
          calc
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y))) ++
              [H.x.val[2 * k + 2 + n]]).length
                =
                (List.map Prod.fst
                  ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                    (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y)))).length + 1 := by
                  simp
            _ ≤ n + 1 := by
              exact Nat.add_le_add_right hlen_map _
        have hshort' :
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y))) ++
              [H.x.val[2 * k + 2 + n]]).length ≤ hL.1.mk.minLength - (2 * k + 2) :=
          le_trans hylen hn'
        have hshort :
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y))) ++
              [H.x.val[2 * k + 2 + n]]).length
              ≤ (hL.1.mk.takeMin.x.val.drop (2 * k + 2)).length := by
          have hdrop_len :
              (hL.1.mk.takeMin.x.val.drop (2 * k + 2)).length =
                hL.1.mk.minLength - (2 * k + 2) := by
            simp [LLift.takeMin_x_coe, List.length_drop, List.length_take, Nat.min_eq_left hmin_le]
          rw [hdrop_len]
          exact hshort'
        have hshort'' :
            (List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦
                    (a,
                      subAt
                        (pullSub (subAt G.tree hL.1.mk.takeMin.x.val)
                          (hL.1.mk.takeMin.x.val.drop (2 * k + 2)))
                        y))) ++
              [H.x.val[2 * k + 2 + n]]).length
              ≤ (hL.1.mk.takeMin.x.val.drop (2 * k + 2)).length := by
          simpa [LLift.toWLLift] using hshort
        have hy :
            List.map Prod.fst
                ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                  (fun a y ↦
                    (a,
                      subAt
                        (pullSub (subAt G.tree hL.1.mk.takeMin.x.val)
                          (hL.1.mk.takeMin.x.val.drop (2 * k + 2)))
                        y))) ++
              [H.x.val[2 * k + 2 + n]] <+:
              hL.1.mk.takeMin.x.val.drop (2 * k + 2) ∧
            [] ∈ subAt G.tree hL.1.mk.takeMin.x.val := by
          constructor
          · simp [← List.zipInitsMap_map]; rw [List.getElem_drop', List.take_concat_get']
            simp [List.drop_take]
            have hmin := hL.1.mk.le_minLength
            omega
          · simpa only [mem_subAt, List.append_nil, LLift.takeMin_x_coe] using hL.1.mk.takeMin.x.prop
        exact (@mem_pullSub_short _
          (subAt G.tree hL.1.mk.takeMin.x.val)
          (hL.1.mk.takeMin.x.val.drop (2 * k + 2))
          (List.map Prod.fst
            ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
              (fun a y ↦
                (a,
                  subAt
                    (pullSub (subAt G.tree hL.1.mk.takeMin.x.val)
                      (hL.1.mk.takeMin.x.val.drop (2 * k + 2)))
                    y))) ++
            [H.x.val[2 * k + 2 + n]]) hshort'').2 hy
      · rw [mem_pullSub_long (by as_aux_lemma => simp; omega)]
        use ((H.x.val.drop (2 * k + 2)).drop (hL.1.mk.minLength - (2 * k + 2))).take
          (2 * k + n + 3 - hL.1.mk.minLength), by
          apply take_mem ⟨_, _⟩; simp
        conv => lhs; simp [← List.zipInitsMap_map]; rw [List.getElem_drop', List.take_concat_get']
        erw [List.drop_take, ← List.take_add, List.take_eq_take_iff, List.length_drop]
        have := hL.1.mk.le_minLength; omega
@[simps toWLLift] def toLLift' : WLLift' hyp where
  toWLLift := hL.1.mk.toWLLift
  hlift := by
    have h := hL.lift_mem (H.x.val.length - (2 * k + 2))
    rwa [List.take_of_length_le (by simp)] at h
attribute [simp_lengths] toLLift'_toWLLift
end Lost

namespace Losable
variable {H : Lift hyp} (h : H.Losable)
lemma extend {h} (hL : (H.take n h).Losable) (hc : H.ConLong) : H.Losable := by
  use hc; apply WinningPrefix.of_take; simpa [Losable, List.drop_take] using hL.2
lemma losable_of_le {H H' : Lift hyp} (h : H.Losable) (h' : H ≤ H') (hc : H'.ConLong) :
  H'.Losable := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h; exact h.extend hc
lemma take (hn : 1 ≤ h.2.num + n) :
  (H.take (2 * k + 1 + h.2.num + n) (by as_aux_lemma => omega)).Losable := by
  use H.conLong_take (h := by omega) h.1
  replace h := h.2; simp [List.drop_take] at h ⊢
  apply WinningPrefix.of_take (n := h.num)
  simpa (disch := omega) [List.take_take] using h.shrink
@[simps] def x' : (H.game.residual ((H.x.val.drop (2 * k + 1)).take h.2.num)).tree where
  val := H.x.val.drop (2 * k + 1 + h.2.num)
  property := by simpa using h.1
attribute [simp_lengths] x'_coe
section
variable (hp : IsPosition H.x.val Player.zero)
def a : ExtensionsAt h.x' := h.2.strat h.x' (by have := H.hlvl; synth_isPosition)
def extension : ExtensionsAt H.x where
  val := (h.a hp).val
  property := by simpa [subAt, ← List.append_assoc] using H.game_tree_sub (h.a hp).prop
@[simps] def extensionPreLift : PreLift hyp where
  x := (h.extension hp).valT'
  R := H.R
  hlvl := by simp
lemma extensionPreLift_take :
  (h.extensionPreLift hp).take H.x.val.length H.hlvl = H.toPreLift := by
  ext1 <;> simp
@[simp] lemma extensionPreLift_game : (h.extensionPreLift hp).game = H.game := by
  rw [← h.extensionPreLift_take hp]; simp
@[simps! toPreLift] def extensionLift : Lift hyp where
  toPreLift := h.extensionPreLift hp
  h'lvl := by
    have hlen : H.x.val.length ≤ (h.extensionPreLift hp).x.val.length := by
      simp [extensionPreLift, extension, ExtensionsAt.val'_length]
    exact le_trans H.h'lvl hlen
  conShort := by rw [← PreLift.conShort_iff_take, extensionPreLift_take]; exact H.conShort; exact H.hlvl
lemma extensionLift_take :
  (h.extensionLift hp).take H.x.val.length H.h'lvl = H := by
  ext1; apply extensionPreLift_take
lemma extension_losable hp : (h.extensionLift hp).Losable := by
  apply extend; rw [extensionLift_take]; exact h
  unfold PreLift.ConLong
  simp [extension, ExtensionsAt.val']
  rw [List.drop_append_of_le_length (by
    have hlen := H.h'lvl
    omega)]
  simpa [← List.append_assoc] using (h.a hp).prop
end
end Losable

variable (H : Lift hyp) (hp : IsPosition H.x.val Player.zero)
  (R : ResStrategy ⟨_, T'⟩ Player.zero H.x.val.length)
def extension : ExtensionsAt H.x :=
  if h : H.Lost then h.toLLift'.extensionMap hp R
  else if h : H.Losable then h.extension hp
  else if h : H.Winnable then h.toWLift'.extensionMap hp R
  else choice (hyp.pruned H.x)
lemma extension_winnable (h : H.Winnable) :
  H.extension hp R = h.toWLift'.extensionMap hp R := by
  unfold extension; split_ifs with h' h'
  · cases h (h'.1.mk.losable h.conLong).2
  · cases h h'.2
  · rfl
end Lift

end
end GaleStewartGame.BorelDet.Zero
