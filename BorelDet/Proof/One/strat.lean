import BorelDet.Proof.One.lift

namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section

def stratMap (lvl : ℕ) (R : ResStrategy ⟨_, T'⟩ Player.one lvl) :
  ResStrategy ⟨_, T⟩ Player.one lvl := fun x hp hlen ↦
  if _ : x.val.length ≤ 2 * k then (ResStrategy.fromMap π) (R.res hlen) x hp le_rfl
  else
    let pL : PreLift hyp := ⟨x, by omega, R.res (by omega)⟩
    pL.extension hp (R.res hlen)
def stratMap' (R : Strategy T' Player.one) : Strategy G.tree Player.one :=
  fun x hp ↦ stratMap x.val.length ((strategyEquivSystem R).str _) x hp le_rfl
lemma stratMap'_short R x hp (hx : x.val.length ≤ 2 * k) :
  stratMap' R x hp = (ResStrategy.fromMap π) ((strategyEquivSystem («T» := ⟨_, T'⟩) R).str _)
    x hp le_rfl := by
  simp [stratMap', stratMap, hx]

variable (hyp) in
@[ext 900] structure TreeLift where
  Rx : Σ R, (stratMap' (hyp := hyp) R).pre.subtree
  --R := Rx.1--TODO x causes weird performance problems
  --x := Rx.2
  --R : Strategy T' Player.one
  --x : (stratMap' R).pre.subtree
  hlvlR : 2 * k + 1 ≤ Rx.2.val.length (α := no_index _)
namespace TreeLift
variable (H : TreeLift hyp)
def R := H.Rx.1
def x : (stratMap' H.R).pre.subtree := H.Rx.2
@[ext] lemma ext' {H H' : TreeLift hyp} (hR : H.R = H'.R) (hx : H.x.val = H'.x.val) : H = H' := by
  simp [R, x] at hR hx; ext <;> simp [*]
@[simp] lemma hlvl : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := H.hlvlR
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
@[simps!] def preLift : PreLift hyp := ⟨subtree_incl _ H.x,
  H.hlvl, (strategyEquivSystem H.R).str (2 * k + 1)⟩
attribute [simp_lengths] preLift_x_coe
@[simps] def take (n : ℕ) (hk : 2 * k + 1 ≤ n) : TreeLift hyp where
  Rx := ⟨H.R, Tree.take n H.x⟩
  hlvlR := by simp [hk]
@[simp] lemma take_R {h} : (H.take n h).R = H.R := rfl
@[simp, simp_lengths] lemma take_x {h} : (H.take n h).x = Tree.take n H.x := rfl
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by ext1 <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by ext1 <;> simp [min_comm]
@[simp] lemma preLift_take hk : (H.take n hk).preLift = H.preLift.take n hk := by ext <;> simp
def extension hp := H.preLift.extension hp ((strategyEquivSystem H.R).str _)
@[congr] lemma extension_val_congr {H H' : TreeLift hyp} (h : H = H') {hp} :
  (H.extension hp).val = (H'.extension (by subst h; exact hp)).val := by congr!
lemma stratMap'_extend : stratMap' H.R (subtree_incl _ H.x) = H.extension := by
  ext hp; dsimp [stratMap', stratMap]; split_ifs with h
  · have := H.hlvl; omega
  · rfl
@[simps!] def dropLast (h : 2 * k + 2 ≤ H.x.val.length) := H.take (H.x.val.length - 1) (by omega)
@[simp] lemma dropLast_R {h} : (H.dropLast h).R = H.R := rfl
@[simp, simp_lengths] lemma dropLast_x {h} :
  (H.dropLast h).x = Tree.take (H.x.val.length - 1) H.x := rfl

lemma x_mem_tree h (hp : IsPosition H.x.val Player.zero) :
  H.x.val[H.x.val.length - 1]'(by as_aux_lemma => have := H.hlvl; omega)
  = ((H.dropLast h).extension (by as_aux_lemma => synth_isPosition)).val := by
  have hx := H.x.prop
  simp_rw (config := {singlePass := true})
    [H.x.val.eq_take_concat (H.x.val.length - 1) (by as_aux_lemma => have := H.hlvl; omega)] at hx
  replace hx := subtree_compatible _ (Tree.take _ H.x) (by as_aux_lemma => synth_isPosition) hx
  simp at hx; change _ = stratMap' (H.dropLast h).R ⟨(H.dropLast h).x.val, _⟩ _ at hx
  erw [stratMap'_extend] at hx; apply_fun Subtype.val at hx; exact hx
lemma x_mem_tree' h (hp : IsPosition H.x.val Player.zero) :
  H.preLift.x = ((H.dropLast h).extension (by as_aux_lemma => synth_isPosition)).valT' := by
  ext1; simp [ExtensionsAt.val']; rw [← H.x_mem_tree h hp, ← List.eq_take_concat]; omega

lemma losable_or_winnable :
  H.preLift.Losable ∨ H.preLift.Winnable := by
  let ⟨n, hn⟩ := le_iff_exists_add.mp H.hlvl
  induction' n with n ih generalizing H
  · suffices H.preLift.Losable ∨ H.preLift.Winnable ∨ H.preLift.Won by --TODO how can this be more powerful than the plain have for subsequent tauto?
      have (h : H.preLift.Won) : H.preLift.Winnable := (PreLift.WLift.mk _ h).winnable; tauto
    have := Lift.con_of_short (hyp := hyp); tauto
  · let Ht := H.dropLast (by synth_isPosition)
    rcases ih Ht (by dsimp [Ht]; synth_isPosition) with ih | ih
    · have : ¬ H.preLift.Winnable → ¬ Ht.preLift.Winnable := by
        intro hw h; apply hw; exact h.winnable_of_le (by simp [Ht, dropLast])
      have : ¬ H.preLift.Won → ¬ Ht.preLift.Won := by
        intro hw h; apply hw; exact h.won_of_le (by simp [Ht, dropLast])
      suffices H.preLift.Losable ∨ H.preLift.Winnable ∨ H.preLift.Won by
        have (h : H.preLift.Won) : H.preLift.Winnable := (PreLift.WLift.mk _ h).winnable; tauto
      suffices ¬ Ht.preLift.Winnable → ¬ Ht.preLift.Won → ¬ H.preLift.Winnable
        → H.preLift.Losable' → H.preLift.Losable by tauto
      intro hnW hnW' hnW'' h; use h
      by_cases IsPosition H.x.val Player.one
      · let HL := PreLift.LLift.mk _ h
        by_cases hc : HL.toLift.Con
        · exact hc
        · have hlif : (PreLift.LLift.mk _ ih.1).toLift =
            HL.toLift.take (2 * k + 1 + n) (by as_aux_lemma => omega) := by
            ext1
            · simp [HL, Ht, dropLast, hn]
            · dsimp [HL, PreLift.LLift.S]; congr! 1; simp [Ht, dropLast]
          have ⟨hcs, hcl⟩ :=
            (Lift.con_short_long _ (by simp [Ht]; synth_isPosition)).mp ih.lift'.con
          simp [hlif, List.drop_take] at hcs hcl
          simp [HL.toLift.con_short_long (by dsimp [HL]; synth_isPosition),
            Ht, dropLast, List.drop_take, hn, hcs] at hc
          have hnat1 : 2 * k + 1 + n - (2 * k + 2) = n - 1 := by omega
          rw [hnat1] at hcl
          have hnat3 : n - 1 + 1 = n := by synth_isPosition
          have hnat2 : 2 * k + 1 + n = 2 * k + 2 + (n - 1) := by omega
          have hlist : HL.toLift.liftShort.val[2 * k + 1].1
            :: ((H.x.val.drop (2 * k + 2)).take (n - 1)
            ++ [H.x.val[2 * k + 1 + n]]) = H.x.val.drop (2 * k + 1) := by
            simp_rw [hnat2]; nth_rw 2 [List.getElem_drop']
            rw [List.take_concat_get', (H.x.val.drop _).take_of_length_le (by synth_isPosition)]
            simp [hcs, HL]
          have hcm := HL.concat_mem_tree (a := H.x.val[2 * k + 1 + n]) (by
            unfold HL; synth_isPosition) (by
            simpa [hlist, HL] using subtree_sub _ H.x.prop) hcl (by
              intro h; apply hnW''; use n + 1
              simp [WinningPosition] at h
              convert h using 2
              · simp [hlist, hn, HL]
              · synth_isPosition)
          simp [hnat2, HL] at hcm
          rw [List.getElem_drop', List.take_concat_get', List.take_of_length_le
            (by synth_isPosition)] at hcm
          cases hc hcm
      · convert (ih.lift'.extensionLift' (by simp [Ht]; synth_isPosition)
          ((strategyEquivSystem H.R).str _) (by simp [Ht])).con
        ext1
        · ext1
          · simpa [extension, PreLift.extension, hnW, hnW', ih, Ht] using
              H.x_mem_tree' (by as_aux_lemma => omega) (by as_aux_lemma => synth_isPosition)
          · rfl
        · dsimp [PreLift.LLift.S]; congr! 1; simp [Ht, dropLast]
    · exact Or.inr (ih.winnable_of_le (by simp [Ht, dropLast]))

lemma x_mem_tree_short' (h : n ≤ 2 * k) (hp : IsPosition (H.x.val.take n) Player.one) :
  Tree.take (n + 1) (pInv π (Tree.take (2 * k) (subtree_incl _ H.x))) =
  (H.R (pInv π (subtree_incl _ (Tree.take n H.x)))
    (by as_aux_lemma => synth_isPosition)).valT' := by
  have hx := (Tree.take (n + 1) H.x).prop; have := H.hlvl
  rw [take_coe, ← List.take_concat_get' _ _ (by as_aux_lemma => omega)] at hx
  replace hx := subtree_compatible _ (Tree.take n H.x) hp hx
  simp only [subtree_incl_coe, take_coe, Set.mem_singleton_iff] at hx
  rw [stratMap'_short _ _ _ (by
    simp only [subtree_incl_coe, take_coe, List.length_take, min_le_iff, h, true_or])] at hx
  apply_fun Subtype.val at hx; simp at hx
  apply Fixing.inj (f := π) (ht := by as_aux_lemma => synth_fixing)
  ext1; simp_rw [take_apply π]; simp [List.take_take]
  rw [min_eq_left (by as_aux_lemma => synth_isPosition)]
  rw [← List.take_concat_get', hx, ExtensionsAt.val', List.map_append]; congr
  · show _ = (π _).val; simp
  · simp [ResStrategy.fromMap]; rfl
lemma x_mem_tree_short (h : n < 2 * k) (hp : IsPosition (H.x.val.take n) Player.one) :
  (pInvTreeHom_map hyp (H.x.val.take (2 * k)))[n]'(by simpa [Nat.lt_iff_add_one_le]) =
  (H.R (pInv π ((stratMap' H.R).pre.subtree_incl (Tree.take n H.x))) (by simpa)).val := by
  have h := congr_arg (fun x ↦ x.val[n]?) (H.x_mem_tree_short' h.le hp)
  simp at h; apply Option.some_injective
  erw [← List.getElem?_eq_getElem, h, List.getElem?_eq_getElem]
  erw [ExtensionsAt.val'_get_last_of_eq _ (by have := H.hlvl; synth_isPosition)]

lemma get_eq_get_take (hn : n < H.x.val.length) (hk : 2 * k ≤ n) : H.x.val[n] =
  (H.take (n + 1) (by as_aux_lemma => omega)).x.val[(H.take (n + 1) (by as_aux_lemma => omega)).x.val.length - 1]'
    (by as_aux_lemma => simp; omega) := by simp; congr; omega
set_option maxHeartbeats 400000 in
lemma wLift_mem_tree (h : H.preLift.Won) : h.lift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using h.lift'.lift.prop)
  have := H.hlvl; intro n _ _ _ _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · show _ = H.R (Tree.take n h.lift'.lift) _; ext1
    have hl := H.x.prop.2 (y := H.x.val.take n) (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
      (by simpa using List.take_prefix _ _) (by as_aux_lemma => synth_isPosition)
    simp [stratMap'] at hl
    conv => lhs; simp (config := {singlePass := true}) only [List.getElem_take' _ hn',
      Lift.liftVal_take_short]
    simp [Lift.liftVeryShort]
    rw [List.getElem_append_left (by as_aux_lemma => synth_isPosition)]
    erw [H.x_mem_tree_short (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
    congr!
    · rw [pInv_treeHom_val _ _ (by as_aux_lemma => synth_isPosition), Lift.liftVal_take_init]
      · simp
      · omega
    apply Fixing.inj (f := π) (ht := by as_aux_lemma => synth_fixing); ext1; simp
    erw [h.lift'.liftVal_lift]; dsimp
  rcases hn'.eq_or_gt with rfl | hn'
  · simp; apply Subtype.ext; conv => lhs; simp [Lift.liftVal]
    split_ifs
    · synth_isPosition
    · rw [List.getElem_append_left (by synth_isPosition)]
      simp [Lift.liftShort, strategyEquivSystem]
      rw [ExtensionsAt.val'_get_last_of_eq _ (by simp)]
      congr! <;> [skip; ext1] <;> simp
  · apply extensionsAt_ext_fst (x := Tree.take n h.lift'.lift) _ _ (by as_aux_lemma => synth_isPosition)
    by_cases hW : (H.take n (by as_aux_lemma => omega)).preLift.Won
    · rw [h.lift'.liftVal_lift_get (by as_aux_lemma => synth_isPosition)]; simp
      rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
        x_mem_tree _ (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
      dsimp [extension, PreLift.extension]; split
      · simp [Lift'.extensionMap, Lift'.extension, strategyEquivSystem]
        congr! <;> [skip; ext1] <;> (
          simp only [dropLast, take_coe, take_trans, preLift_take, Lift'.lift_coe,
            PreLift.Losable.lift'_toLift, subtree_incl_coe]
          rw [← Lift.liftVal_take _ _ (by as_aux_lemma => omega)]
          congr 1; ext1
          · simp; congr; synth_isPosition
          · apply PreLift.WLift.toLift_mono; simp)
      · rename_i _ hif; cases hif (by as_aux_lemma => simp [dropLast] at hW ⊢; convert hW; synth_isPosition)
    · let H' := PreLift.WLift.mk _ h; have hux := H'.u_spec'
      have hul : H'.u.val.length > n - (2 * k + 1) := by
        simp [PreLift.Won] at hW; by_contra
        cases hW H'.u (by simp)
          (List.prefix_of_prefix_length_le hux ((List.take_prefix _ _).drop _)
          (by have := hux.length_le; synth_isPosition))
      show _ = (H.R ⟨h.lift'.liftVal.take n, _⟩ _).val.1
      generalize_proofs _ _ pf2
      have hR := mem_getTree (H.R ⟨h.lift'.liftVal.take n, pf2⟩ (by
        synth_isPosition)).valT'
      simp at hR
      rw [ExtensionsAt.val'_take_of_le _ (by as_aux_lemma => synth_isPosition)] at hR
      simp (disch := omega) [List.take_take] at hR
      erw [h.lift'.liftVal_take_short (by as_aux_lemma => synth_isPosition)] at hR
      erw [H'.getTree_liftShort] at hR
      simp at hR
      rw [mem_pullSub_short (by as_aux_lemma => synth_isPosition)] at hR
      replace hR := hR.1; simp [List.prefix_iff_eq_take] at hR
      conv => rhs; erw [← ExtensionsAt.val'_get_last,
        ← List.getElem_map Prod.fst (h := by simp)]
      simp_rw (config := {singlePass := true}) [PreLift.Won.lift'_toLift, hR]
      simp; erw [List.getElem_append_right (by as_aux_lemma => synth_isPosition)]
      conv => lhs; erw [h.lift'.liftVal_lift_get (by as_aux_lemma => synth_isPosition)]
      simp
      rw [List.prefix_iff_eq_take] at hux; simp_rw (config := {singlePass := true}) [hux]
      simp; congr; synth_isPosition

lemma lLift_mem_tree (h : H.preLift.Losable) :
  h.lift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using h.lift'.lift.prop)
  have := H.hlvl; intro n _ _ _ _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · show _ = H.R (Tree.take n h.lift'.lift) _; ext1
    have hl := H.x.prop.2 (y := H.x.val.take n) (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
      (by simpa using List.take_prefix _ _) (by as_aux_lemma => synth_isPosition)
    simp [stratMap'] at hl
    conv => lhs; simp (config := {singlePass := true}) only [List.getElem_take' _ hn',
      Lift.liftVal_take_short]
    simp [Lift.liftVeryShort]
    rw [List.getElem_append_left (by synth_isPosition)]
    erw [H.x_mem_tree_short (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
    congr!
    · rw [pInv_treeHom_val _ _ (by synth_isPosition), Lift.liftVal_take_init]
      · simp
      · omega
    apply Fixing.inj (f := π) (ht := by as_aux_lemma => synth_fixing); ext1; simp
    erw [h.lift'.liftVal_lift]; dsimp
  rcases hn'.eq_or_gt with rfl | hn'
  · simp; apply Subtype.ext; conv => lhs; simp [Lift.liftVal]
    split_ifs
    · synth_isPosition
    · rw [List.getElem_append_left (by synth_isPosition)]
      simp [Lift.liftShort, strategyEquivSystem]
      rw [ExtensionsAt.val'_get_last_of_eq _ (by simp)]
      congr! <;> [skip; ext1] <;> simp
  · apply extensionsAt_ext_fst (x := Tree.take n h.lift'.lift) _ _ (by as_aux_lemma => synth_isPosition)
    rw [h.lift'.liftVal_lift_get (by synth_isPosition)]; simp
    rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition)]
    unfold extension
    rw [PreLift.extension_losable (h := h.losable_of_le (by simp [dropLast]))]
    simp [Lift'.extensionMap, Lift'.extension, strategyEquivSystem]
    congr! <;> [skip; ext1] <;> (
      simp only [dropLast, take_coe, take_trans, preLift_take, Lift'.lift_coe,
        PreLift.Losable.lift'_toLift, subtree_incl_coe]
      rw [← Lift.liftVal_take _ _ (by as_aux_lemma => omega)]
      congr 1; ext1
      · simp_rw [PreLift.LLift.toLift_toPreLift, Lift.take_toPreLift]; congr; synth_isPosition
      · dsimp [PreLift.LLift.S]; congr! 1; rw [PreLift.game_take])

lemma take_winnable (h : H.preLift.Winnable) n :
  (H.take (2 * k + 1 + h.num + n) (by as_aux_lemma => omega)).preLift.Winnable :=
  h.takeMin_winnable.winnable_of_le (by simp [PreLift.Winnable.takeMin, - PreLift.instLE_le])
lemma winnable_subtree (hL : H.preLift.Winnable) (hnL : ¬ ∃ h, (H.dropLast h).preLift.Won) :
  H.x.val.drop (2 * k + 1 + hL.num) ∈ hL.strat.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa [PreLift.game_tree] using subtree_sub _ H.x.prop)
  intro n hn _ _ _; simp at hn ⊢
  have htr := (H.take (2 * k + 1 + hL.num + n + 1) (by as_aux_lemma => omega)).x_mem_tree
    (by as_aux_lemma => synth_isPosition) (by as_aux_lemma => synth_isPosition); simp at htr
  simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel] at htr
  apply Subtype.ext; dsimp; rw [htr]
  simp only [dropLast, take_R, take_x, take_coe, List.length_take, take_trans, tsub_le_iff_right,
    min_le_iff, le_add_iff_nonneg_right, zero_le, true_or, min_eq_right,
    preLift_x_coe, residual_tree]; simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel]
  have := H.take_winnable hL n
  dsimp [extension, PreLift.extension]; split_ifs with hi
  · cases hnL ⟨by synth_isPosition, by
      apply hi.won_of_le; simp [dropLast, - PreLift.instLE_le]; rw [hL.prefix_num _ (by simp) rfl]
      · omega
      · rfl⟩
  · symm; unfold PreLift.Winnable.extension PreLift.Winnable.a PreLift.Winnable.x'
    apply this.prefix_strat_apply' ((List.take_prefix _ _).drop _) (by simp) rfl
    · simp [List.take_drop]; generalize_proofs pf
      nth_rw 1 [pf.prefix_num ((List.take_prefix _ _).drop _) (by simp) rfl]
end TreeLift

variable {R : Strategy (gameAsTrees hyp).2 Player.one} (y : body (stratMap' R).pre.subtree)
@[simps] def bodyTake (n : ℕ) : TreeLift hyp where
  Rx := ⟨R, body.take (2 * k + 1 + n) y⟩
  hlvlR := by simp
@[simp] lemma bodyTake_R : (bodyTake y n).R = R := rfl
@[simp] lemma bodyTake_x : (bodyTake y n).x = body.take (2 * k + 1 + n) y := rfl
@[simp] lemma bodyTake_take (h : 2 * k + 1 ≤ m) :
  (bodyTake y n).take m (by omega) = bodyTake y (min (m - (2 * k + 1)) n) := by
  ext1 <;> simp; congr; omega
attribute [simp_lengths] bodyTake_x
@[simp] lemma takeLift_mono : (bodyTake y m).preLift ≤ (bodyTake y n).preLift ↔ m ≤ n := by
  constructor <;> intro h
  · simpa using PreLift.length_mono h
  · ext1
    · ext1; simp [h]
    · rfl
@[simp] lemma takeLift_wonPos : (bodyTake y n).preLift.WonPos = (bodyTake y 0).preLift.WonPos := by
  rw [← (takeLift_mono y).mpr (Nat.zero_le n), PreLift.wonPos_take]
@[simp] lemma takeLift_game : (bodyTake y n).preLift.game = (bodyTake y 0).preLift.game := by
  rw [← (takeLift_mono y).mpr (Nat.zero_le n), PreLift.game_take]

set_option maxHeartbeats 400000 in
lemma won_of_winnable n (h : (bodyTake y n).preLift.Winnable) :
  ∃ m, (bodyTake y m).preLift.Won := by
  by_cases h' : ∃ m, (bodyTake y m).preLift.Won; exact h'
  have hb : (body.drop (2 * k + 1 + h.num) y).val ∈ body h.strat.pre.subtree := by
    apply mem_body_of_take (n + 1); intro m hm
    have := (bodyTake y (h.num + m)).winnable_subtree
      (h.winnable_of_le (by simp [- PreLift.instLE_le]; omega))
      (by
        simp [TreeLift.dropLast, - TreeLift.preLift_take] at h' ⊢; intro _
        rw [bodyTake_take _ (by omega)]; apply h')
    simp [Stream'.take_drop] at this ⊢; generalize_proofs pf1 pf2 pf3 at this
    rw [h.prefix_strat_subtree (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synth_isPosition)).drop _)
      (by simp) rfl] at this
    simp_rw [add_assoc] at this ⊢; convert this using 4
    exact (WinningPrefix.prefix_num _
      (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synth_isPosition)).drop _) (by simp) rfl).symm
  have hw := h.strat_winning hb
  simp only [takeLift_game, TreeLift.preLift_x_coe, bodyTake_R, bodyTake_x, body.take_coe, id_eq,
    residual_tree, Player.payoff_residual, Player.residual_residual, List.length_append,
    List.length_take, List.length_drop, Stream'.length_take, add_tsub_cancel_left, div_add_self,
    Player.residual_even, Player.payoff_zero, subAt_body_image, body.drop_coe, Set.mem_preimage,
    Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hw
  simp [PreLift.game_tree, PreLift.game_payoff] at hw
  obtain ⟨u, hu1, hu2⟩ := hw.2
  use u.length; simp [PreLift.Won]; use u, hu1
  simp [← Stream'.take_drop, List.prefix_iff_eq_take, Stream'.take_take, - Function.iterate_succ]
  rw [principalOpen_iff_restrict] at hu2; convert hu2 using 2
  simp [List.take_drop]; rw [← Stream'.drop_append_of_le_length _ _ _ (by simp)]
  generalize_proofs pf; suffices pf.num ≤ n by simp [this]
  convert h.num_le_length using 1
  · nth_rw 2 [pf.prefix_num (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synth_isPosition)).drop _)
    (by simp) rfl]
  · simp

def wonLift (h : (bodyTake y n).preLift.Won) : body R.pre.subtree :=
  have h' k : (bodyTake y (n + k)).preLift.Won := h.won_of_le ((takeLift_mono y).mpr (by omega))
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
    ⟨(h' k).lift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y _).wLift_mem_tree _⟩, by
    simp; omega⟩⟩, fun k ↦
      ((Lift.liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))
        (PreLift.WLift.toLift_mono ((takeLift_mono y).mpr (Nat.le_succ _)))).take k).trans
      ((h' (k + 1)).lift'.liftVal.take_prefix_take_left (Nat.le_succ _))⟩
lemma wonLift_map (h : (bodyTake y n).preLift.Won) :
  (bodyFunctor.map π ⟨(wonLift y h).val, body_mono R.pre.subtree_sub (wonLift y h).prop⟩).val
  = y.val := by
  ext; simp [wonLift, - PreLift.Won.lift'_toLift, Stream'.get, Stream'.map]
  rw [Lift'.liftVal_lift_get] <;> simp [Stream'.get]; omega
def lostLift (h : ∀ n, (bodyTake y n).preLift.Losable) : body R.pre.subtree :=
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
    ⟨(h k).lift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y _).lLift_mem_tree _⟩, by
    simp⟩⟩, fun k ↦
      ((Lift.liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))
        (PreLift.LLift.toLift_mono ((takeLift_mono y).mpr (Nat.le_succ _)))).take k).trans
      ((h (k + 1)).lift'.liftVal.take_prefix_take_left (Nat.le_succ _))⟩
lemma lostLift_map (h : ∀ n, (bodyTake y n).preLift.Losable) :
  (bodyFunctor.map π ⟨(lostLift y h).val, body_mono R.pre.subtree_sub (lostLift y h).prop⟩).val
  = y.val := by
  ext; simp [lostLift, - PreLift.Losable.lift'_toLift, Stream'.get, Stream'.map]
  rw [Lift'.liftVal_lift_get] <;> simp [Stream'.get]; omega

lemma body_stratMap {G : Game A} {k : ℕ} {hyp : Hyp G k}
  {R : Strategy (gameAsTrees hyp).2 Player.one} (y : body (stratMap' R).pre.subtree) :
  ∃ x : body R.pre.subtree, (bodyFunctor.map π
    ⟨x.val, body_mono R.pre.subtree_sub x.prop⟩).val = y.val :=
  if h : ∀ n, (bodyTake y n).preLift.Losable then ⟨lostLift y h, lostLift_map y h⟩
  else by
    obtain ⟨n, h⟩ := by simpa using h
    have : ∃ n, (bodyTake y n).preLift.Won := by
      have := (bodyTake y n).losable_or_winnable; have := won_of_winnable y n; tauto
    let ⟨n, h⟩ := this
    exact ⟨wonLift y h, wonLift_map y h⟩

end
end GaleStewartGame.BorelDet.One
