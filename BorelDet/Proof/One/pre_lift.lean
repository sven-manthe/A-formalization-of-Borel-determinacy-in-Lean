import BorelDet.Proof.covering_closed_game
import BorelDet.Proof.win_asap

namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section

variable (hyp) in
@[ext] structure PreLift where
  x : T
  hlvl : 2 * k < x.val.length (α := no_index _)
  R : ResStrategy ⟨_, T'⟩ Player.one (2 * k + 1)
namespace PreLift
variable (H : PreLift hyp)
attribute [simp] hlvl
@[simp] lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by simp
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
lemma gameTree_eq : subAt (getTree (pInv π (Tree.take (2 * k) H.x)).val) [H.x.val[2 * k]'H.hlvl] =
  subAt T (H.x.val.take (2 * k + 1)) := by simp

@[simps] def take (n : ℕ) (h : 2 * k < n) : PreLift hyp where
  x := Tree.take n H.x
  hlvl := by simp [h]
  R := H.R
attribute [simp_lengths] take_x
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1 <;> [ext1; skip] <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [min_comm]

@[simps] instance : LE (PreLift hyp) where
  le p q := q.take p.x.val.length p.hlvl = p
lemma length_mono {p q : PreLift hyp} (h : p ≤ q) : p.x.val.length ≤ q.x.val.length := by --why not valid gcongr lemma? (probably multiple functions)
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
end PreLift

variable (hyp) in
@[ext (flat := false)] structure Lift extends PreLift hyp where
  liftTree : tree A
  htree : ∃ S : QuasiStrategy (subAt T (x.val.take (2 * k + 1))) Player.one, liftTree = S.1.subtree
@[simps] instance : Preorder (Lift hyp) where
  le p q := p.toPreLift ≤ q.toPreLift
  le_refl _ := le_rfl (α := PreLift hyp)
  le_trans _ _ _ := le_trans (α := PreLift hyp)
namespace Lift
variable (H : Lift hyp)
def liftVeryShort : T' where
  val := (pInv π (Tree.take (2 * k) H.x)).val ++ [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]
  property := by
    simp [- pInv_treeHom_val]
    simp [H.x.val.take_concat_get' (2 * k) (by have := H.hlvl; omega), Tree.take_mem]
    rw [H.gameTree_eq]; exact H.htree
@[simp, simp_lengths] lemma liftVeryShort_length :
  H.liftVeryShort.val.length (α := no_index _) = 2 * k + 1 := by simp [liftVeryShort]
@[simp] lemma liftVeryShort_val_map :
  H.liftVeryShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 1) := by
  simp [liftVeryShort, pInvTreeHom_map, ← List.zipInitsMap_map]
def liftShort : T' := (H.R H.liftVeryShort (by synth_isPosition) (by simp)).valT'
@[simp, simp_lengths] lemma liftShort_length :
  H.liftShort.val.length (α := no_index _) = 2 * k + 2 := by simp [liftShort]
@[simp] lemma liftShort_val_take :
  H.liftShort.val.take (α := no_index _) (2 * k + 1) = H.liftVeryShort := by
  simp [liftShort, ExtensionsAt.val']
def liftVal := if H.x.val.length = 2 * k + 1 then H.liftVeryShort.val
  else H.liftShort.val ++
  (H.x.val.drop (2 * k + 2)).zipInitsMap (fun a y ↦ ⟨a, subAt (getTree H.liftShort.val) y⟩)
lemma liftVal_very_short (h : H.x.val.length = 2 * k + 1) : H.liftVal = H.liftVeryShort.val := by
  unfold liftVal; split_ifs; rfl
@[simp, simp_lengths] lemma liftVal_length :
  H.liftVal.length (α := no_index _) = H.x.val.length := by
  have := H.hlvl; simp [liftVal]; split_ifs <;> synth_isPosition
@[simp] lemma liftVal_take_short (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftVal.take (α := no_index _) (2 * k + 2) = H.liftShort.val := by
  unfold liftVal; split_ifs
  · omega
  · simp
@[simp] lemma liftVal_take_veryShort :
  H.liftVal.take (α := no_index _) (2 * k + 1) = H.liftVeryShort.val := by
  simp [liftVal, liftShort]; split_ifs
  · simp
  · rw [List.take_append_of_le_length (by simp), ExtensionsAt.val'_take_of_eq _ (by simp)]
@[simp] lemma liftVal_take_init (h : n ≤ 2 * k) :
  H.liftVal.take (α := no_index _) n = pInvTreeHom_map hyp (H.x.val.take n) := by
  have : n = min n (2 * k + 1) := by omega
  rw [this, ← List.take_take, liftVal_take_veryShort]
  simp [liftVeryShort, pInvTreeHom_map, List.take_append,
      List.zipInitsMap_take, List.take_take, h, ← this]
-- for u drop (2 * k + 1)
def PreWonPos (u : List A) := LosingCondition H.liftShort.val (by simp) ∧
  (∃ (h : u ≠ []), u[0]'(by simpa [List.length_pos_iff]) = H.liftShort.val[2 * k + 1].1) ∧
  getTree H.liftShort.val = pullSub (subAt T (H.x.val.take (2 * k + 1) ++ u)) u.tail

@[simps toPreLift liftTree] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift hyp where
  toPreLift := H.toPreLift.take n (by omega)
  liftTree := H.liftTree
  htree := by
    obtain ⟨S, hS⟩ := H.htree; use cast (by simp [List.take_take, h]) S
    rw [hS]; symm; apply cast_subtree (by simp [List.take_take, h]) rfl
attribute [simp_lengths] take_toPreLift
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply PreLift.take_of_length_le <;> omega; rfl
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp; rfl
@[simp] lemma liftVeryShort_take h : (H.take n h).liftVeryShort = H.liftVeryShort := by
  ext1; simp [liftVeryShort, (by omega : 2 * k ≤ n)]
@[simp] lemma liftShort_take h : (H.take n h).liftShort = H.liftShort := by
  ext1; simp [liftShort]; congr! 1; rw [H.liftVeryShort_take]; congr!
@[simp] lemma liftVal_take n h :
  (H.take n h).liftVal = H.liftVal.take n := by
  unfold Lift.liftVal; split_ifs
  · simpa
  · have : n = 2 * k + 1 := by synth_isPosition
    rw [List.take_append_of_le_length (by simp [this])]; simp [this]
  · synth_isPosition
  · simp [List.take_append, List.drop_take, List.zipInitsMap_take]
    have := H.hlvl; synth_isPosition
@[simp] lemma preWonPos_take h u :
  (H.take n h).PreWonPos u ↔ H.PreWonPos u := by simp [PreWonPos, List.take_take, h]
lemma take_le {h} : H.take n h ≤ H := H.toPreLift.take_le (h := h)
@[simp] lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n :=
  H.toPreLift.take_le_take hm hn
lemma eq_take {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H = H'.take H.x.val.length (by simp) := by ext1; symm; exact h; exact ht
lemma liftVal_mono {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H.liftVal <+: H'.liftVal := by rw [eq_take h ht]; simpa using List.take_prefix _ _

def Con := H.x.val.drop (2 * k + 1) ∈
  pullSub (getTree H.liftShort.val) [H.liftShort.val[2 * k + 1].1]
lemma Con.take h (h' : H.Con) : (H.take n h).Con := by
  simpa [Lift.Con, List.drop_take] using take_mem ⟨_, h'⟩
lemma con_of_short (h : H.x.val.length = 2 * k + 1) : H.Con := by
  simpa [Con, ← h] using (getTree_ne_and_pruned _).1
lemma con_short_long (h : 2 * k + 2 ≤ H.x.val.length) : H.Con ↔
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] ∧
  H.x.val.drop (2 * k + 2) ∈ getTree H.liftShort.val := by
  simp [Con, pullSub, List.take_one_drop_eq_of_lt_length h, eq_comm]
end Lift

variable (hyp) in
@[ext (flat := false)] structure Lift' extends Lift hyp where
  con : toLift.Con
instance : Preorder (Lift' hyp) where
  le p q := p.toLift ≤ q.toLift
  le_refl _ := le_rfl (α := Lift hyp)
  le_trans _ _ _ := le_trans (α := Lift hyp)
namespace Lift'
variable (H : Lift' hyp)
lemma conShort (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] :=
  ((H.con_short_long h).mp H.con).1
lemma conLong : H.x.val.drop (2 * k + 2) ∈ getTree H.liftShort.val := by
  simpa [add_comm, ← add_assoc] using H.con.2
@[simp] lemma liftShort_val_map (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 2) := by
  rw [H.liftShort.val.eq_take_concat (2 * k + 1) (by simp),
    List.map_append, List.map_singleton, H.conShort h]
  simp [Lift.liftShort, ExtensionsAt.val']
@[simp] lemma liftVal_lift : H.liftVal.map (α := no_index _) Prod.fst = H.x.val := by
  unfold Lift.liftVal; split_ifs <;>
    simp (disch := have := H.hlvl; omega) [← List.zipInitsMap_map, *]
@[simp] lemma liftVal_lift_get (h : n < H.x.val.length) :
  (H.liftVal[n]'(by simp [h])).1 = H.x.val[n]'(by simpa) := by
  simp_rw [← liftVal_lift, List.getElem_map, upA]

@[simps toLift] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift' hyp where
  toLift := H.toLift.take n (by omega)
  con := H.con.take _ _
attribute [simp_lengths] take_toLift
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply Lift.take_of_length_le <;> omega
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp

@[simps] def lift : T' where
  val := H.liftVal
  property := by
    let ⟨n, hn⟩ := le_iff_exists_add.mp (Nat.add_one_le_iff.mpr H.hlvl)
    induction' n with n ih generalizing H
    · simp [Lift.liftVal, hn]
    · specialize ih (H.take (2 * k + 1 + n) (by omega)); simp [hn] at ih
      rcases n with _ | n
      · simp at hn; simp [Lift.liftVal, ← hn]; simp [hn]
      · rw [H.liftVal.eq_take_concat (2 * k + 1 + (n + 1)) (by synth_isPosition)]
        have hnat : 2 * k + 1 + (n + 1) = (2 * k + 2) + n := by omega
        simp [- List.take_append_getElem]; use ih; constructor
        · simp [getTree_eq' _ ih, hn]
          simp_rw [hnat]; rw [List.getElem_drop', ← List.take_drop, List.take_concat_get']
          simpa (disch := omega) [List.take_take] using take_mem ⟨_, H.conLong⟩
        · split_ifs
          · synth_isPosition
          · synth_isPosition
          · conv => lhs; unfold Lift.liftVal
            simp [hn]
            rw [List.getElem_append_right (by synth_isPosition), getTree_eq' _ ih]
            simp (disch := omega) [List.take_take, hnat]; congr 2
            rw [← List.take_drop, List.getElem_drop', List.take_concat_get']
@[simp] lemma lift_lift : π H.lift = H.x := tree_ext H.liftVal_lift
attribute [simp_lengths] lift_coe
end Lift'

namespace PreLift
variable (H : PreLift hyp)
@[simps toPreLift liftTree] def extend --weird simps! error message
  (S : QuasiStrategy (subAt T (H.x.val.take (2 * k + 1))) Player.one) : Lift hyp where
  toPreLift := H
  liftTree := S.1.subtree
  htree := ⟨S, rfl⟩
attribute [simp_lengths] extend_toPreLift
def WonPos := {u | ∃ S, (H.extend S).PreWonPos u}
@[simps (config := {isSimp := false})] def game : Game A where
  tree := subAt T (H.x.val.take (2 * k + 1))
  payoff := Subtype.val⁻¹' ⋃ u ∈ H.WonPos, principalOpen u
lemma game_open : IsOpen H.game.payoff := IsOpen.preimage
  continuous_subtype_val (isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ principalOpen_isOpen _)
lemma extend_take h S : (H.take n h).extend S =
  (H.extend (cast (by simp [List.take_take, h]) S)).take n h := by
  ext1; rfl; simp [extend]; symm; apply cast_subtree (by simp [List.take_take, h]) rfl
@[simp] lemma wonPos_take h : (H.take n h).WonPos = H.WonPos := by
  ext; simp [WonPos, extend_take]
  generalize_proofs pf; rw [(cast_bijective pf).surjective.exists]
@[simp] lemma game_take h : (H.take n h).game = H.game := by
  ext1 <;> simp [game, List.take_take, h]
def Won := ∃ u ∈ H.WonPos, u <+: H.x.val.drop (2 * k + 1)
def Winnable := WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
def Losable' := ¬ WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
end PreLift
