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
        have : (H.x.val.drop (2 * k + 1)).take 1 = [H.liftNode] := by
          rw [List.take_one_drop_eq_of_lt_length (by simp [Nat.lt_iff_add_one_le])]; rfl
        simpa only [this] using hS)
    simp_rw [pullSub_body, Set.image_subset_iff]
    apply subset_trans h; simp [PreLift.game_payoff]
    intro _
    simp [Lift.liftNode, ← Stream'.append_eq_cons, ← Stream'.append_append_stream]
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
        simp [List.take_take, toWLift]
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
    simpa [liftNode, WLLift'.extensionMap, ExtensionsAt.map_val' π] using hm'.1
  simp [PreLift.ConLong]; convert hm using 1
  rw [← List.getElem_cons_drop _ _ (by simp [Nat.lt_iff_add_one_le])]; congr 1
  rw [List.getElem_take' (j := 2 * k + 2), H.x.val.getElem_take' (j := 2 * k + 2)] <;> simp
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
  rw [Set.eq_empty_iff_forall_not_mem] at *; rintro ⟨x, hx⟩ ⟨hx', hxp⟩
  simp [Nat.add_mod] at hx hx' hxp; apply hL ⟨x, by
    simpa [← Stream'.append_append_stream] using body_mono H.game_tree_sub hx⟩
  simp; convert hxp.1 using 1; ext1; simp [← Stream'.append_append_stream, hxp.2]
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
      simp
      rw [← List.getElem_take, List.getElem_cons_drop]
      simp [Nat.sub_eq_zero_iff_le, Nat.lt_iff_add_one_le]⟩ hL.2
  · simp; left; rw [LosingCondition.concat]
    refine ⟨?_, ⟨hL.1.mk.takeMin.x.val.drop (2 * k + 2), ?_⟩, ?_⟩
    · simp [LLift.toWLLift]; rw [← Set.subset_empty_iff]
      rintro _ ⟨⟨z, hzb, hze⟩, ⟨_, _, rfl⟩⟩
      apply (wonPosition_iff_disjoint'.mp hL.1.mk.min_prefix).subset ⟨_, by simpa⟩
      use ⟨z, by simpa⟩; ext1
      simp [← Stream'.append_append_stream, H.liftShort_val_map] at hze
      rw [List.drop_take, ← List.take_add] at hze
      simpa using hze
    · rw [LLift.takeMin_x_coe]; simp; rw [List.getElem_take', List.getElem_cons_drop]
      · simpa [PreLift.ConLong] using hL.2
      · simp [Nat.lt_iff_add_one_le]
    · simp [LLift.toWLLift]
      rw [List.append_cons, List.take_concat_get', List.drop_take, ← List.take_add]
      simp
lemma lift_mem n : hL.1.mk.toWLLift.liftMediumVal ++
  ((H.x.val.drop (2 * k + 2)).take n).zipInitsMap
  (fun a y ↦ ⟨a, subAt hL.1.mk.toWLLift.liftTree y⟩) ∈ T' := by
  induction' n with n ih
  · simpa using hL.liftMedium_mem
  · simp only [List.take_succ, List.zipInitsMap_append, List.getElem?_drop,
      WLLift.getTree_liftMediumVal, oldAsTrees_fst] at ih ⊢
    by_cases hn : 2 * k + 2 + n ≥ H.x.val.length
    · erw [List.getElem?_eq_none_iff.mpr hn]
      simpa only [Option.toList_none, List.zipInitsMap_nil, List.append_nil] using ih
    · rw [List.getElem?_eq_getElem (by abstract omega)]; simp [← List.append_assoc]
      use ih; rw [getTree_eq' _ ih]
      refine ⟨?_, by simp [← List.zipInitsMap_map]⟩
      rw [List.take_left' (WLLift.liftMediumVal_length _)]
      simp only [LLift.toWLLift, LLift.takeMin_x_coe,
        WLLift.getTree_liftMediumVal, WLLift.liftMediumVal_length, List.drop_left', mem_subAt]
      by_cases hn : 2 * k + 2 + n + 1 ≤ hL.1.mk.minLength
      · rw [mem_pullSub_short (by abstract simp; omega)]; constructor
        · simp [← List.zipInitsMap_map]; rw [List.getElem_drop', List.take_concat_get']
          simp [List.drop_take]; omega
        · simpa only [mem_subAt, List.append_nil, LLift.takeMin_x_coe] using hL.1.mk.takeMin.x.prop
      · rw [mem_pullSub_long (by abstract simp; omega)]
        use ((H.x.val.drop (2 * k + 2)).drop (hL.1.mk.minLength - (2 * k + 2))).take
          (2 * k + n + 3 - hL.1.mk.minLength), by
          apply take_mem ⟨_, _⟩; simp
        conv => lhs; simp [← List.zipInitsMap_map]; rw [List.getElem_drop', List.take_concat_get']
        erw [List.drop_take, ← List.take_add, List.take_eq_take, List.length_drop]
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
  (H.take (2 * k + 1 + h.2.num + n) (by abstract omega)).Losable := by
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
  h'lvl := by simp
  conShort := by rw [← PreLift.conShort_iff_take, extensionPreLift_take]; exact H.conShort
lemma extensionLift_take :
  (h.extensionLift hp).take H.x.val.length H.h'lvl = H := by
  ext1; apply extensionPreLift_take
lemma extension_losable hp : (h.extensionLift hp).Losable := by
  apply extend; rw [extensionLift_take]; exact h
  unfold PreLift.ConLong
  simp [extension, ExtensionsAt.val']
  rw [List.drop_append_of_le_length (by simp)]
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
