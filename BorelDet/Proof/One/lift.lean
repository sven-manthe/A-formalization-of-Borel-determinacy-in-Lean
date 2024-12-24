import BorelDet.Proof.One.pre_lift

namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section

namespace Lift'
variable (H : Lift' hyp) (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy ⟨_, T'⟩ Player.one H.x.val.length) (hR : R.res (by simp) = H.R)
def extension := R H.lift (by synth_isPosition) (by simp)
def extensionMap := ExtensionsAt.map π H.lift_lift (H.extension hp R)
@[simp] lemma extension_take :
  (H.extension hp R).val' (A := no_index _).take (α := no_index _) (H.x.val.length (α := no_index _))
  = H.liftVal := by rw [ExtensionsAt.val'_take_of_eq _ (by simp)]; dsimp
@[simp] lemma extensionMap_take (h : n ≤ H.x.val.length) :
  (H.extensionMap hp R).val' (A := no_index _).take (α := no_index _) n
  = H.x.val.take n := by simpa [ExtensionsAt.val']
@[simps] def extensionLift : Lift hyp where
  x := (H.extensionMap hp R).valT'
  R := H.R
  hlvl := by simp
  liftTree := H.liftTree
  htree := by
    obtain ⟨S, hS⟩ := H.htree;  use cast (by simp [List.take_take]) S
    rw [hS]; symm; apply cast_subtree (by simp [List.take_take]) rfl
@[simp] lemma extensionLift_take :
  (H.extensionLift hp R).take (H.x.val.length (α := no_index _)) (by simp) = H.toLift := by
  ext1 <;> [ext1; skip] <;> simp [extensionMap, ← take_apply π]
@[simp] lemma extensionLift_liftShort : (H.extensionLift hp R).liftShort = H.liftShort := by
  rw [← extensionLift_take, Lift.liftShort_take]
@[simp] lemma extensionLift_wonPos : (H.extensionLift hp R).WonPos = H.WonPos := by
  rw [← extensionLift_take]; simp; rfl
@[simps! toLift] def extensionLift' : Lift' hyp where
  toLift := H.extensionLift hp R
  con := by
    have h := (H.extension hp R).prop; simp at h; replace h := h.2.1
    erw [getTree_eq H.lift] at h; simp at h
    simp [Lift.Con, ExtensionsAt.val']
    by_cases hl : H.x.val.length = 2 * k + 1
    · nth_rw 1 [mem_pullSub_short (by synth_isPosition), List.drop_append_eq_append_drop]
      simp [← hl, (getTree_ne_and_pruned H.liftShort).1, extensionMap]
      simp [Lift.liftShort, extension, ← hR, ResStrategy.res]
      rw [ExtensionsAt.val'_get_last_of_eq _ (by simpa)]
      congr! <;> [skip; apply Subtype.ext] <;> simp [H.liftVal_very_short hl]
    · have := H.hlvl; rw [mem_pullSub_long (by synth_isPosition)]
      use H.x.val.drop (2 * k + 2) ++ [(H.extension hp R).val.1]; constructor
      · simpa (disch := omega) using h
      · rw [← List.append_assoc, List.drop_append_of_le_length H.hlvl]; congr
        · erw [← List.getElem_map Prod.fst (h := by simp)]
          simp (disch := omega) [- List.getElem_map]
        · simp [extensionMap]
attribute [simp_lengths] extensionLift_x extensionLift'_toLift
@[simp] lemma extensionLift'_game : (H.extensionLift' hp R hR).game = H.game := by
  ext <;> simp [PreLift.game]
@[simp] lemma extensionLift'_take :
  (H.extensionLift' hp R hR).take (H.x.val.length (α := no_index _)) (by simp) = H := by
  ext1; apply extensionLift_take
end Lift'

namespace PreLift
lemma Losable'.losable'_of_le {H H' : PreLift hyp} (hL : H'.Losable') (h : H ≤ H') :
  H.Losable' := by
  intro hW; apply hL; rw [← h] at hW; simp [List.drop_take] at hW; exact hW.of_take
variable (hyp) in
structure LLift extends PreLift hyp where
  los : toPreLift.Losable'
namespace LLift
variable (H : LLift hyp)
def S := defensiveQuasi H.game Player.one (hyp.pruned.sub _)
lemma S_winning : H.S.1.IsWinning :=
  H.game.gale_stewart_precise' H.game_open (hyp.pruned.sub _) (by
    intro h; apply H.los; use 0; simpa)
@[simps! toPreLift liftTree] def toLift := H.extend H.S
attribute [simp_lengths] toLift_toPreLift
lemma toLift_mono {H H' : LLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.toLift.liftTree = H'.toLift.liftTree := by simp [S]; congr! 1; rw [← h]; simp
lemma winning_condition : WinningCondition H.toLift.liftShort.val (by simp) := by
  rw [← not_losing]; apply _root_.not_imp_self.mp; intro hlos
  unfold LosingCondition; simp [Set.eq_empty_iff_forall_not_mem]
  intro _ u hu1 hu2; simp [Lift.liftVeryShort] at hu1
  let qS : QuasiStrategy (H.game.residual _).tree _ :=
    (H.game.defensiveQuasi Player.one (hyp.pruned.sub _)).residual
    (H.toLift.liftShort.val[2 * k + 1].1 :: u)
  have := not_imp_not.mpr (AllWinning.existsWinning (hP := (hyp.pruned.sub _).sub _))
    ((existsWinning_iff_quasi.mpr ⟨qS, H.S_winning.residual ⟨_, hu1⟩⟩).not_both_winning
    (by simpa using subtree_sub _ hu1))
  simp [AllWinning, Set.not_subset] at this
  obtain ⟨a, ha, ⟨a', ha', haa'⟩, hap⟩ := this
  simp [← haa', - Set.mem_image, game_payoff] at hap
  specialize hap (H.toLift.liftShort.val[2 * k + 1].1 :: u) (by
    unfold WonPos; use defensiveQuasi H.game Player.one (hyp.pruned.sub _)
    unfold Lift.PreWonPos; simp; use of_not_not hlos, rfl
    rw [List.append_cons]
    convert hu2 using 4
    conv => rhs; rw [H.toLift.liftShort.val.eq_take_concat (2 * k + 1) (by simp),
      List.map_append, List.map_singleton]
    simp [Lift.liftShort, ExtensionsAt.val'])
  apply hap; use a'
lemma concat_mem_tree {y a} (hp : IsPosition y Player.zero)
  (ha : H.x.val.take (2 * k + 1) ++ H.toLift.liftShort.val[2 * k + 1].1 :: (y ++ [a]) ∈ T)
  (hy : y ∈ getTree H.toLift.liftShort)
  (hw : ¬ H.game.WinningPosition (H.toLift.liftShort.val[2 * k + 1].1 :: y ++ [a])) :
  y ++ [a] ∈ getTree H.toLift.liftShort := by
  obtain ⟨_, S', hS⟩ := H.winning_condition
  rw [hS] at hy ⊢; rw [subtree_fair _ ⟨_, hy⟩ hp]; simp [Lift.liftVeryShort]
  rw [← List.cons_append, subtree_compatible_iff _ ⟨_, by
    simpa [Lift.liftVeryShort] using hy.1⟩ (by synth_isPosition)]
  simpa [ha, S, defensiveQuasi, tryAndElse, defensivePre, preserveProp] using fun _ ↦ hw
end LLift
def Losable (H : PreLift hyp) := ∃ h : H.Losable', (LLift.mk _ h).toLift.Con
lemma Losable.losable_of_le {H H' : PreLift hyp} (hL : H'.Losable) (h : H ≤ H') :
  H.Losable := by
  use hL.1.losable'_of_le h; (conv => rhs; rhs; lhs; rw [← h])
  convert hL.2.take (n := H.x.val.length) (h := by simp); ext1
  · simp
  · simp only [LLift.toLift_liftTree, LLift.S, Lift.take_liftTree]; congr! 1; simp

@[simps toLift] def Losable.lift' {H : PreLift hyp} (h : H.Losable) := Lift'.mk _ h.2
attribute [simp_lengths] Losable.lift'_toLift

lemma Won.won_of_le {H H' : PreLift hyp} (hW : H.Won) (h : H ≤ H') : H'.Won := by
  rw [← h, Won, wonPos_take, take_x, take_coe, List.drop_take] at hW
  obtain ⟨u, hu, h⟩ := hW; exact ⟨u, hu, h.trans <| List.take_prefix _ _⟩
variable (hyp) in
structure WLift extends PreLift hyp where
  won : toPreLift.Won
namespace WLift
variable (H : WLift hyp)
lemma winnable : H.Winnable := by
  let ⟨u, hu, hux⟩ := H.won; use u.length
  apply AllWinning.existsWinning _ ((hyp.pruned.sub _).sub _)
  rw [List.prefix_iff_eq_take] at hux
  simpa [AllWinning, game_payoff, Set.eq_univ_iff_forall, ← hux] using
    fun a _ ↦ ⟨u, ⟨hu, principalOpen_append_nil a u⟩⟩
lemma exists_prefix : ∃ n h, (H.take n h).Won := ⟨H.x.val.length, by simpa using H.won⟩
def minLength := Nat.find H.exists_prefix
@[simp] lemma minLength_le : H.minLength ≤ H.x.val.length (α := no_index _) :=
  Nat.find_le ⟨H.hlvl, by simpa using H.won⟩
@[simp] lemma le_minLength : 2 * k + 1 ≤ H.minLength := (Nat.find_spec H.exists_prefix).1
@[simp] lemma le_minLength' : 2 * k ≤ H.minLength := le_trans (Nat.le_succ _) H.le_minLength
@[simps!] def takeMin := H.take H.minLength H.le_minLength
@[simp] lemma takeMin_wonPos : H.takeMin.WonPos = H.WonPos := by simp [takeMin]
lemma min_prefix : H.takeMin.Won := (Nat.find_spec H.exists_prefix).2
def u : H.WonPos := ⟨H.min_prefix.choose, by simpa using H.min_prefix.choose_spec.1⟩
def S := H.u.prop.choose
lemma u_spec : H.u.val <+: H.takeMin.x.val.drop (2 * k + 1) := H.min_prefix.choose_spec.2
lemma u_spec' : H.u.val <+: H.x.val.drop (2 * k + 1) :=
  H.u_spec.trans <| (List.take_prefix _ _).drop _
lemma u_nil : H.u.val ≠ [] := H.u.prop.choose_spec.2.1.1
@[simp] lemma getTree_liftShort : getTree (H.extend H.S).liftShort.val =
  pullSub (subAt T (H.x.val.take (2 * k + 1) ++ H.u.val)) H.u.val.tail :=
  H.u.prop.choose_spec.2.2
@[simps! toPreLift liftTree] def toLift := H.extend H.S
lemma u_zero : H.u.val[0]'(by simpa [List.length_pos] using H.u_nil)
  = H.toLift.liftShort.val[2 * k + 1].1 := H.u.prop.choose_spec.2.1.2
@[simps! toLift] def toLift' : Lift' hyp where
  toLift := H.toLift
  con := by
    simp [Lift.Con]; erw [WLift.getTree_liftShort]; simp
    have := H.hlvl; have hu := H.u_spec'
    by_cases hl : H.x.val.length = 2 * k + 1
    · rw [mem_pullSub_short (by simp [hl])]; simp [← hl]
      show H.u.val ∈ subAt T H.x.val
      apply mem_of_prefix hu; simp [← hl]
    · rw [mem_pullSub_long (by
        have := hu.length_le; synth_isPosition)]
      obtain ⟨z, hz⟩ := hu; use z; simp [hz]
      rw [← (H.x.val.drop _).head_cons_tail (by synth_isPosition)]
      congr
      · simp [List.head_drop, ← WLift.u_zero]
        show H.x.val[(2 * k + 1) + 0] = _
        rw [List.getElem_drop']; simp_rw [← hz]; rw [List.getElem_append_left]
      · apply_fun List.tail at hz; simp at hz; simp [← hz]
        simp [List.tail_append, WLift.u_nil]
attribute [simp_lengths] toLift_toPreLift toLift'_toLift

universe u v in
lemma hEq_fst {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v}
  (x : @PSigma α β) (y : @PSigma α' β') (h : α = α') (h' : HEq β β') (h'' : HEq x y) :
  HEq x.fst y.fst := by subst h; cases h'; cases h''; rfl
lemma minLength_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.minLength = H'.minLength := by
  apply le_antisymm
  · apply Nat.find_le; use H'.le_minLength; convert H'.min_prefix
    rw [← h]; simp; congr; simp
    apply Nat.find_le; use H.hlvl; rw [h]; exact H.won
  · apply Nat.find_mono; intro n ⟨hn, hW⟩; use hn
    apply hW.won_of_le; rw [← h]; simp; congr 1; have := length_mono h; omega
lemma takeMin_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.takeMin = H'.takeMin := by unfold takeMin; simp_rw [← minLength_eq_le h]; rw [← h]; simp
lemma u_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) : HEq H.u H'.u := by
  unfold u; congr! 1
  · congr! 2; rw [← h]; simp
  · congr! 1; rw [takeMin_eq_le h]
@[simp] lemma u_min_prefix : (WLift.mk _ H.min_prefix).u.val = H.u.val := by
  have := u_eq_le (H := WLift.mk _ H.min_prefix) (H' := H) (by simp [takeMin])
  rwa [Subtype.heq_iff_coe_eq (by simp)] at this
lemma uprop' : (WLift.mk _ H.min_prefix).u.val ∈ H.takeMin.WonPos := by simp
lemma uprop'_choose : HEq H.u.prop.choose H.uprop'.choose := by
  congr 1
  · simp [List.take_take]
  · congr! 1 with S1 S2 heq
    · simp [List.take_take]
    · rw [← cast_eq_iff_heq (e := by simp [List.take_take])] at heq
      have : (H.extend S1).liftShort = (H.takeMin.extend S2).liftShort := by
        simp [takeMin, extend, Lift.liftShort, Lift.liftVeryShort]; congr! 5
        · apply Subtype.ext; simp
        · simp
        · rw [← heq]; symm; apply cast_subtree; simp [List.take_take]; rfl
      simp [Lift.PreWonPos]; congr! 6
      · congr!
      · simp [List.take_take]
  · apply proof_irrel_heq
lemma toLift_liftTree' : H.toLift.liftTree = H.uprop'.choose.1.subtree := by
  simp only [toLift_liftTree, S]; congr! 1; simp [List.take_take]
  apply hEq_fst; simp [List.take_take]; congr!; exact H.uprop'_choose
lemma toLift_mono {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.toLift.liftTree = H'.toLift.liftTree := by
  simp_rw [toLift_liftTree']; have hu := u_eq_le h; rw [Subtype.heq_iff_coe_eq] at hu
  congr! 1
  · rw [takeMin_eq_le h]
  · apply hEq_fst
    · rw [takeMin_eq_le h]
    · congr!
    · congr 1
      · congr; congr!
      · congr! 3
        · rw [takeMin_eq_le h]
        · congr! 3; rw [takeMin_eq_le h]
        · congr! 2; rw [takeMin_eq_le h]
      · apply proof_irrel_heq
  rw [← h]; simp
end WLift
@[simps! toLift] def Won.lift' {H : PreLift hyp} (h : H.Won) := (WLift.mk _ h).toLift'
attribute [simp_lengths] Won.lift'_toLift

namespace Winnable
lemma winnable_of_le  {H H' : PreLift hyp} (hW : H.Winnable) (h : H ≤ H') : H'.Winnable := by
  rw [← h] at hW; simp [Winnable, List.drop_take] at hW; exact hW.of_take
variable {H : PreLift hyp} (h : H.Winnable)
@[simps!] def takeMin := H.take (2 * k + 1 + h.num) (by omega)
lemma takeMin_winnable : h.takeMin.Winnable := by
  simpa [Winnable, takeMin, List.drop_take] using h.shrink
@[simps] def x' : (H.game.residual ((H.x.val.drop (2 * k + 1)).take h.num)).tree :=
  ⟨H.x.val.drop (2 * k + 1 + h.num), by simp [game]⟩
attribute [simp_lengths] x'_coe
variable (hp : IsPosition H.x.val Player.one)
def a : ExtensionsAt h.x' := h.strat h.x' (by have := H.hlvl; synth_isPosition)
def extension : ExtensionsAt H.x where
  val := (h.a hp).val
  property := by
    have h' := (h.a hp).prop; simp [game] at h' ⊢
    simp_rw [← List.drop_drop _ (2 * k + 1), ← List.append_assoc _ _ [_],
      List.take_append_drop] at h'; exact h'
end Winnable

def extension (H : PreLift hyp) (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy ⟨_, T'⟩ Player.one H.x.val.length) : ExtensionsAt H.x :=
  if h : H.Won then h.lift'.extensionMap hp R
  else if h : H.Winnable then h.extension hp
  else if h : H.Losable then h.lift'.extensionMap hp R
  else choice (hyp.pruned H.x)
lemma extension_losable {H : PreLift hyp} (h : H.Losable) hp R :
  H.extension hp R = h.lift'.extensionMap hp R := by
  unfold extension; split_ifs with h' h'
  · cases h.1 (WLift.mk _ h').winnable
  · cases h.1 h'
  · rfl
end PreLift

end
end GaleStewartGame.BorelDet.One
