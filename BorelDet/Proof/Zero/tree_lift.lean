import BorelDet.Proof.Zero.lift

namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section

def stratMap (lvl : ℕ) (R : ResStrategy ⟨_, T'⟩ Player.zero lvl) :
  ResStrategy ⟨_, T⟩ Player.zero lvl := fun x hp hlen ↦
  if _ : x.val.length ≤ 2 * k then (ResStrategy.fromMap π) (R.res hlen) x hp le_rfl
  else
    let pL : PreLift hyp := ⟨x, by omega, R.res (by omega)⟩
    if hpL : pL.ConShort
    then (Lift.mk pL (by unfold pL; synth_isPosition) hpL).extension hp (R.res hlen)
    else choice (hyp.pruned x)
def stratMap' (R : Strategy T' Player.zero) : Strategy G.tree Player.zero :=
  fun x hp ↦ stratMap x.val.length ((strategyEquivSystem R).str _) x hp le_rfl
lemma stratMap'_short R x hp (hx : x.val.length ≤ 2 * k) :
  stratMap' R x hp = (ResStrategy.fromMap π) ((strategyEquivSystem («T» := ⟨_, T'⟩) R).str _)
    x hp le_rfl := by simp [stratMap', stratMap, hx]

variable (hyp) in
@[ext 900] structure TreeLift where
  R : Strategy T' Player.zero
  x : (stratMap' R).pre.subtree
  hlvl : 2 * k < x.val.length (α := no_index _)
namespace TreeLift
@[ext] lemma ext' {H H' : TreeLift hyp} (hR : H.R = H'.R) (hx : H.x.val = H'.x.val) : H = H' := by
  ext <;> [skip; rw [Subtype.heq_iff_coe_heq]] <;> simp [*]
variable (H : TreeLift hyp)
attribute [simp] hlvl
@[simp] lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
@[simps!] def preLift : PreLift hyp := ⟨subtree_incl _ H.x,
  H.hlvl, (strategyEquivSystem H.R).str (2 * k)⟩
attribute [simp_lengths] preLift_x_coe
@[simps] def take (n : ℕ) (hk : 2 * k < n) : TreeLift hyp where
  R := H.R
  x := Tree.take n H.x
  hlvl := by simp [hk]
attribute [simp_lengths] preLift_x_coe take_x
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by ext1 <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by ext1 <;> simp [min_comm]
@[simp] lemma preLift_take hk : (H.take n hk).preLift = H.preLift.take n hk := by ext <;> simp
lemma conShort : H.preLift.ConShort := by
  dsimp [PreLift.ConShort, strategyEquivSystem, preLift,
    PreLift.liftShort, ResStrategy.res, res.val', ExtensionsAt.val']
  rw [List.getElem_append_right (by simp)]
  simpa [stratMap', stratMap, strategyEquivSystem, ResStrategy.fromMap] using
    congr_arg Subtype.val <| subtree_compatible _ (Tree.take (2 * k) H.x)
    (a := H.x.val[2 * k]'H.hlvl) (by have := H.hlvl'; synth_isPosition) (by simp [Tree.take_mem])
@[simps toPreLift] def lift (h : 2 * k + 2 ≤ H.x.val.length) : Lift hyp where
  toPreLift := H.preLift
  h'lvl := h
  conShort := H.conShort
attribute [simp_lengths] lift_toPreLift
def extension (hp : IsPosition H.x.val Player.zero) :=
  (H.lift (by have := H.hlvl; synth_isPosition)).extension hp ((strategyEquivSystem H.R).str _)
@[congr] lemma extension_val_congr {H H' : TreeLift hyp} (h : H = H') {hp} :
  (H.extension hp).val = (H'.extension (by subst h; exact hp)).val := by congr!
@[simp] lemma lift_take hk h' : (H.take n hk).lift h'
  = (H.lift (by simp at h'; exact h'.2)).take n (by simp at h'; exact h'.1) := by
  ext1; simp
lemma stratMap'_extend : stratMap' H.R (subtree_incl _ H.x) = H.extension := by
  ext hp; dsimp [stratMap', stratMap]; split_ifs with h h'
  · have := H.hlvl; omega
  · rfl
  · cases h' H.conShort
@[simps!] def dropLast (h : 2 * k + 2 ≤ H.x.val.length) := H.take (H.x.val.length - 1) (by omega)
attribute [simp_lengths] dropLast_x_coe

lemma x_mem_tree h (hp : IsPosition H.x.val Player.one) :
  H.x.val[H.x.val.length - 1]'(by as_aux_lemma => have := H.hlvl; omega)
  = ((H.dropLast h).extension (by as_aux_lemma => synth_isPosition)).val := by
  have hx := H.x.prop
  simp_rw (config := {singlePass := true})
    [H.x.val.eq_take_concat (H.x.val.length - 1) (by as_aux_lemma => have := H.hlvl; omega)] at hx
  replace hx := subtree_compatible _ (Tree.take _ H.x) (by as_aux_lemma => synth_isPosition) hx
  simp at hx; change _ = stratMap' (H.dropLast h).R ⟨(H.dropLast h).x.val, _⟩ _ at hx
  erw [stratMap'_extend] at hx; apply_fun Subtype.val at hx; exact hx
lemma x_mem_tree' h (hp : IsPosition H.x.val Player.one) :
  H.preLift.x = ((H.dropLast h).extension (by as_aux_lemma => synth_isPosition)).valT' := by
  ext1; simp [ExtensionsAt.val']; rw [← H.x_mem_tree h hp, ← List.eq_take_concat]; omega

lemma conLong_or_lost : H.preLift.ConLong ∨ ∃ h, (H.lift h).Lost := by
  let ⟨n, hn⟩ := le_iff_exists_add.mp H.hlvl_le
  induction' n with n ih generalizing H
  · left
    rw [PreLift.ConLong, ← hn, List.drop_of_length_le (by simp)]
    exact (getTree_ne_and_pruned H.preLift.liftShort).1
  · let Ht := H.dropLast (by omega)
    specialize ih Ht (by simp [Ht, hn])
    by_cases ih' : ∃ h, (Ht.lift h).Lost
    · right; use by omega
      have ⟨h', ih'⟩ := ih'; simp_rw [Ht, dropLast] at ih'
      rw [lift_take _ _ (by simpa [Ht] using h')] at ih'
      apply ih'.extend
    · left; simp [ih'] at ih
      by_cases hp : IsPosition H.x.val Player.zero
      · simp [PreLift.ConLong, Ht, dropLast, preLift_take, List.drop_take, hn] at ih ⊢
        rw [(H.x.val.drop (2 * k + 1)).eq_take_concat n (by simp [hn])]
        apply H.preLift.getTree_fair ih (by simp [IsPosition] at hp ⊢; omega) (by
          simp [- List.getElem_drop]; rw [← H.lift_toPreLift (by omega), Lift.liftShort_val_map]
          simpa [← List.take_add] using subtree_sub _ <| take_mem H.x)
      by_cases ih'' : ∃ h, (Ht.lift h).Losable
      · have hW : (Ht.lift (by dsimp [Ht]; synth_isPosition)).Losable := ih''.2
        simp at ih'
        have hm := H.x_mem_tree' (by as_aux_lemma => omega) (by as_aux_lemma => synth_isPosition)
        simp [extension, Lift.extension, hW, ih', Ht] at hm
        generalize_proofs _ _ hL hp at hm
        convert (hL.extension_losable hp).1; ext1
        · exact hm
        · rfl
      · have hW : (Ht.lift (by dsimp [Ht]; synth_isPosition)).Winnable :=
          fun hW ↦ ih'' ⟨by dsimp [Ht]; synth_isPosition, ⟨ih, hW⟩⟩
        have hm := H.x_mem_tree' (by as_aux_lemma => omega) (by as_aux_lemma => synth_isPosition)
        simp [extension] at hm
        rw [Lift.extension_winnable _ _ _ hW] at hm
        convert hW.extension_conLong (by as_aux_lemma => dsimp [Ht] at *; synth_isPosition)
          ((strategyEquivSystem H.R).str _)
        ext1
        · ext1; simp_rw [hm]; rfl
        · rfl
variable {H} in
lemma lost_of_lost' {h} (hL : (H.lift h).Lost') : (H.lift h).Lost := by
  rcases H.conLong_or_lost with h' | h'
  · use hL; convert H.preLift.conLong_take (h := hL.mk.takeMin.hlvl) h'
    simp [Lift.LLift.takeMin]; congr; simpa using hL.mk.minLength_le
  · exact h'.2

lemma x_mem_tree_short' h' (h : n ≤ 2 * k) (hp : IsPosition (H.x.val.take n) Player.zero) :
  Tree.take (n + 1) (H.lift h').liftShort =
  (H.R (pInv π ((stratMap' H.R).pre.subtree_incl (Tree.take n H.x)))
    (by as_aux_lemma => synth_isPosition)).valT' := by
  have hx := (Tree.take (n + 1) H.x).prop; have := H.hlvl
  rw [take_coe, ← List.take_concat_get' _ _ (by as_aux_lemma => omega)] at hx
  replace hx := subtree_compatible _ (Tree.take n H.x) hp hx
  simp only [subtree_incl_coe, take_coe, Set.mem_singleton_iff] at hx
  rw [stratMap'_short _ _ _ (by
    simp only [subtree_incl_coe, take_coe, List.length_take, min_le_iff, h, true_or])] at hx
  rcases h.lt_or_eq with h | rfl
  · apply_fun Subtype.val at hx; simp at hx
    apply Fixing.inj (f := π) (ht := by as_aux_lemma => synth_fixing)
    ext1; simp_rw [take_apply π, Lift.liftShort_lift, take_coe, List.take_take] --now π is needed
    rw [min_eq_left (by as_aux_lemma => omega)]; simp
    rw [← List.take_concat_get', hx, ExtensionsAt.val', List.map_append]; congr
    · show _ = (π _).val; simp
    · simp [ResStrategy.fromMap]; rfl
    · synth_isPosition
  · ext1
    simp [← List.take_append_getElem, ExtensionsAt.val']; constructor <;> simp [PreLift.liftShort]
    · rw [ExtensionsAt.val'_take_of_eq] <;> simp
    · rw [ExtensionsAt.val'_get_last_of_eq _ (by simp)]; rfl
lemma x_mem_tree_short h' (h : n ≤ 2 * k) (hp : IsPosition (H.x.val.take n) Player.zero) :
  (H.lift h').liftShort.val[n]'(by simpa [Nat.lt_iff_add_one_le]) =
  (H.R (pInv π ((stratMap' H.R).pre.subtree_incl (Tree.take n H.x))) (by simpa)).val := by
  have h := congr_arg (fun x ↦ x.val[n]?) (H.x_mem_tree_short' h' h hp)
  simp at h; apply Option.some_injective
  erw [← List.getElem?_eq_getElem, h, List.getElem?_eq_getElem]
  erw [ExtensionsAt.val'_get_last_of_eq _ (by synth_isPosition)]
  synth_isPosition

def WinnableOrLost := ∃ h, (H.lift h).Winnable ∨ (H.lift h).Lost
variable (hWL : H.WinnableOrLost)
def wLLift' :=
  if hW : (H.lift hWL.1).Winnable then
    hW.toWLift'
  else
    have hL : (H.lift hWL.1).Lost := by unfold WinnableOrLost at hWL; tauto
    hL.toLLift'
@[simp, simp_lengths] lemma wLLift'_to_lift : (H.wLLift' hWL).toLift = H.lift hWL.1 := by
  unfold wLLift'; split_ifs <;> rfl
lemma wLift'_eq_wLLift' {h} (hW : (H.lift h).Winnable) :
  hW.toWLift' = (H.wLLift' ⟨h, Or.inl hW⟩) := by
  unfold wLLift'; split_ifs <;> rfl
lemma lLift'_eq_wLLift' {h} (hL : (H.lift h).Lost) :
  hL.toLLift' = H.wLLift' ⟨h, Or.inr hL⟩ := by
  unfold wLLift'; split_ifs with h
  · cases h (hL.1.mk.losable h.conLong).2
  · rfl

lemma lift_mem_tree_short n (hn : n < 2 * k + 1) hp :
  (H.wLLift' hWL).liftVal[n]'(by as_aux_lemma => simp; have := H.hlvl; omega) =
  (H.R (Tree.take n ((H.wLLift' hWL).lift)) hp).val := by
  have hl := H.x.prop.2 (y := H.x.val.take n) (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
    (by simpa using List.take_prefix _ _) (by as_aux_lemma => synth_isPosition)
  simp [stratMap'] at hl
  conv => lhs; rw [List.getElem_take' _ hn]; simp only [WLLift.liftVal_take_short, wLLift'_to_lift]
  erw [H.x_mem_tree_short _ (by as_aux_lemma => omega) (by as_aux_lemma => synth_isPosition)]; congr!
  apply Fixing.inj (f := π) (ht := by as_aux_lemma => synth_fixing); ext1; simp
lemma wLift'_eq_wLLift'_long {h} (hW : (H.lift h).Winnable) hp : --TODO why needed?
  (H.R (Tree.take n hW.toWLift'.lift) hp).val
  = (H.R (Tree.take n (H.wLLift' ⟨h, Or.inl hW⟩).lift) (by as_aux_lemma => synth_isPosition)).val := by
  simp_rw [wLift'_eq_wLLift']
lemma lLift'_eq_wLLift'_long {h} (hL : (H.lift h).Lost) hp :
  (H.R (Tree.take n hL.toLLift'.lift) hp).val
  = (H.R (Tree.take n (H.wLLift' ⟨h, Or.inr hL⟩).lift) (by as_aux_lemma => synth_isPosition)).val := by
  simp_rw [lLift'_eq_wLLift']

lemma get_eq_get_take (hn : n < H.x.val.length) (hk : 2 * k ≤ n) : H.x.val[n] =
  (H.take (n + 1) (by as_aux_lemma => omega)).x.val[(H.take (n + 1) (by as_aux_lemma => omega)).x.val.length - 1]'
    (by as_aux_lemma => simp; omega) := by simp; congr; omega
lemma wLift_mem_tree h (hW : (H.lift h).Winnable) : hW.toWLift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using hW.toWLift'.hlift)
  intro n _ _ _ _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · show _ = H.R (Tree.take n hW.toWLift'.lift) _; ext1
    simp_rw [wLift'_eq_wLLift', wLift'_eq_wLLift'_long]
    apply H.lift_mem_tree_short _ _ hn'
  · apply extensionsAt_ext_fst (x := Tree.take n hW.toWLift'.lift) _ _ (by as_aux_lemma => synth_isPosition)
    simp; rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
    unfold extension
    rw [Lift.extension_winnable (h := by as_aux_lemma => simpa [dropLast] using hW.take _ _)]
    simp [WLLift'.extensionMap, WLLift'.extension, strategyEquivSystem]
    congr! <;> [skip; ext1] <;>
      simp only [dropLast, take_coe, take_trans, lift_take, WLLift'.lift_coe,
        Lift.Winnable.toWLift'_toWLLift, Lift.liftVal_take, subtree_incl_coe,
        List.take_eq_take_iff] <;> synth_isPosition
--show statements about extension map in common setting?
lemma lLift_mem_tree h (hL : (H.lift h).Lost) : hL.toLLift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using hL.toLLift'.hlift)
  intro n hn _ _ _; simp; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · show _ = H.R (Tree.take n hL.toLLift'.lift) _; apply Subtype.ext
    simp_rw [lLift'_eq_wLLift'_long, ← H.lift_mem_tree_short ⟨h, Or.inr hL⟩ _ hn',
      ← lLift'_eq_wLLift' _ hL]; rfl
  by_cases hL' : (((H.take n (by as_aux_lemma => omega))).lift (by as_aux_lemma => synth_isPosition)).Lost'
  · apply extensionsAt_ext_fst (x := Tree.take n hL.toLLift'.lift) _ _ (by as_aux_lemma => synth_isPosition)
    simp; generalize_proofs --not for performance
    rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
    dsimp [extension, Lift.extension]; split
    · simp [WLLift'.extensionMap, WLLift'.extension, strategyEquivSystem]
      congr! <;> [skip; ext1] <;>
        ( simp only [dropLast, take_R, take_x, take_coe, List.length_take, take_trans, lift_take,
            subtree_incl_coe, WLLift'.lift_coe]
          generalize_proofs _ prf) <;> [skip; replace prf := prf.1] <;>
          ( simp (disch := omega) only [min_eq_left, min_eq_right] at prf
            show _ = ((H.lift h).extend' prf).toWLLift.liftVal.take n
            simp only [Lift.Lost.toLLift'_toWLLift, Lift.liftVal_extend']; congr; omega)
    · rename_i _ hif; cases hif (lost_of_lost' (by
        simp [dropLast] at hL' ⊢; convert hL'; synth_isPosition))
  · simp at hn
    apply extensionsAt_eq_of_lost (x := Tree.take n hL.toLLift'.lift) hL.toLLift'.lift
      (List.take_prefix _ _) (by as_aux_lemma => synth_isPosition)
    · unfold Lift.Lost' at hL'; convert hL' using 2
      · simp
      · synth_isPosition
    · replace hL := hL.1; unfold Lift.Lost' at hL; convert hL using 1
      · simp
      · synth_isPosition

lemma losable_subtree {h} (hL : (H.lift h).Losable) (hnL : ¬ ∃ h', ((H.dropLast h).lift h').Lost) :
  H.x.val.drop (2 * k + 1 + hL.2.num) ∈ hL.2.strat.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using hL.1); intro n hn _ _ _; simp at hn ⊢
  have htr := (H.take (2 * k + 1 + hL.2.num + n + 1) (by as_aux_lemma => omega)).x_mem_tree
    (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition); simp at htr
  simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel] at htr
  apply Subtype.ext; dsimp; rw [htr]
  simp only [dropLast, take_R, take_x, take_coe, List.length_take, take_trans, tsub_le_iff_right,
    min_le_iff, le_add_iff_nonneg_right, zero_le, true_or, min_eq_right, lift_toPreLift,
    preLift_x_coe, residual_tree]; simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel]
  generalize_proofs pf1 pf2
  have : ((H.take (2 * k + 1 + pf1.num + n) pf2).lift (by synth_isPosition)).Losable :=
    hL.take (by synth_isPosition)
  dsimp [extension, Lift.extension]; split_ifs with hi
  · cases hnL ⟨by synth_isPosition, by
      apply hi.lost_of_le; simp [dropLast]; rw [hL.2.prefix_num _ (by simp) rfl]
      · omega
      · rfl⟩
  · symm; unfold Lift.Losable.extension Lift.Losable.a Lift.Losable.x'
    rw [this.2.prefix_strat_apply' ((List.take_prefix _ _).drop _) (by simp) rfl]
    simp [List.take_drop]; congr 2
    generalize_proofs pf3; exact pf3.prefix_num ((List.take_prefix _ _).drop _) rfl rfl
end TreeLift

end
end GaleStewartGame.BorelDet.Zero
