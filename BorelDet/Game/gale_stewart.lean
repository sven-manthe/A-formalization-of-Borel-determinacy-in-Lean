import BorelDet.Game.build_strategies

namespace GaleStewartGame
open Classical
open InfList Tree PreStrategy

variable {A : Type*} {T : Tree A} {G G' : Game A} {p p' : Player}

theorem PreStrategy.cast_quasi {T T' : Tree A} {p p' : Player} (hT : T = T') (hP : p = p')
  (S : PreStrategy T p) :
  (cast (by rw [hT, hP]) S : PreStrategy T' p').IsQuasi ↔ S.IsQuasi := by subst hT hP; rfl
theorem PreStrategy.cast_winning {G G' : Game A} (h : G = G') (S : PreStrategy G.tree p) :
  (cast (by rw [h]) S : PreStrategy G'.tree p).IsWinning
  ↔ S.IsWinning := by subst h; rfl
namespace Game
theorem waiting_equals_pre {G : Game A} {p : Player} (hP : IsPruned G.tree)
  (h : ¬ G.ExistsWinning p.swap) :
  (waitingQuasi G p hP).1.subtree = (waitingPre G p).subtree := by
  refine preserveProp_eq_extQuasi _ ?_ hP ?_ ?_
  · intro x hp nw a; simp [preserveProp, WinningPosition]
    by_contra hc; simp [Set.Nonempty] at hc
    apply nw; rw [WinningPosition, existsWinning_iff_quasi]
    let f (b : A) (h : [b] ∈ ((G.residual x).residual [a.val]).tree) :
      PreStrategy (((G.residual x).residual [a.val]).residual [b]).tree Player.zero :=
      cast (by simp [ExtensionsAt.val']) (hc ⟨b, by simpa [ExtensionsAt.val']⟩).choose.pre
    let S := (sew f).firstMove _ (by exact a.prop)
    use S.extQuasi (hP.sub _); rw [firstMove_extQuasi_isWinning]
    · apply sew_isWinning; intro b h
      rw [cast_winning (G := G.residual _) (by simp [ExtensionsAt.val'])]
      exact (hc ⟨b, by simpa [ExtensionsAt.val']⟩).choose_spec
    · apply sew_isQuasi; intros
      rw [cast_quasi (by simp [ExtensionsAt.val']) rfl]
      apply Strategy.isQuasi
  · rintro rfl; by_contra hc; simp at hc
    apply h; rw [existsWinning_iff_quasi]
    let f (a : A) (h : [a] ∈ G.tree) := (existsWinning_iff_quasi.mp (hc a h)).choose
    use ⟨sew (fun a h ↦ (f a h).1), sew_isQuasi _ (fun a h ↦ (f a h).2)⟩
    apply sew_isWinning (f := fun a h ↦ (f a h).1); intro a ha
    exact (existsWinning_iff_quasi.mp (hc a ha)).choose_spec
  · rintro rfl _; simpa [WinningPosition, ExistsWinning] using h

variable [TopologicalSpace A] [DiscreteTopology A]
theorem isClosed_image_payoff {G : Game A} :
  IsClosed G.payoff ↔ IsClosed (Subtype.val '' G.payoff) :=
  (closedEmbedding_subtype_val (body_isClosed G.tree)).closed_iff_image_closed
theorem waiting_winning_isClosed (hC : IsClosed G.payoff) (hP : IsPruned G.tree) :
  (waitingPre G Player.zero).IsWinning := by
  intro a ha; rw [Player.payoff_zero,
    ← (isClosed_image_payoff.mp hC).closure_eq,
    mem_closure_iff_nhds_basis (hasBasis_basicOpen a)]

  intro x h; by_contra hfa; simp_rw [not_exists, not_and'] at hfa
  specialize ha (a.take (2 * (x.length / 2)) ++ [a (2 * (x.length / 2))]) (by simp [← take_succ'])
  apply (waitingPre G Player.zero).subtree_compatible ⟨_, mem_of_append ha⟩
    (by synth_isPosition) ha
  apply AllWinning.existsWinning _ (hP.sub _); apply wonPosition_iff_disjoint.mpr
  rw [← Set.subset_empty_iff]; intro a' ⟨h1, h2⟩; apply hfa a'
  · simp [← take_succ, ExtensionsAt.val'] at h1; apply basicOpen_mono _ h1
    rw [basicOpen_iff_restrict.mp h]; simp [← take_succ']; omega
  · rw [Player.residual_odd _ _ (by simp; omega)] at h2; simpa using h2

theorem waiting_winning_isOpen (hC : IsOpen G.payoff) (hP : IsPruned G.tree) :
  (waitingPre G Player.one).IsWinning := by
  rw [← sew_residual (waitingPre G Player.one)]; apply sew_isWinning
  simp; intro a _; apply waiting_winning_isClosed
  · simpa using hC.preimage (body.append_con [a])
  · exact hP.sub _
theorem gale_stewart_precise (h : IsClosed G.payoff) (hP : IsPruned G.tree)
  (h' : ¬ G.ExistsWinning Player.one) :
  (waitingQuasi G Player.zero hP).1.IsWinning := by
  dsimp [IsWinning]; rw [waiting_equals_pre hP h' (p := Player.zero)]
  exact waiting_winning_isClosed h hP
theorem gale_stewart (h : IsClosed G.payoff) (hP : IsPruned G.tree) : G.IsDetermined :=
  if h' : _ then ⟨Player.one, h'⟩
  else ⟨Player.zero, existsWinning_iff_quasi.mpr ⟨_, gale_stewart_precise h hP h'⟩⟩
theorem gale_stewart_precise' (h : IsOpen G.payoff) (hP : IsPruned G.tree)
  (h' : ¬ ∃ S : Strategy G.tree Player.zero, S.pre.IsWinning) :
  (waitingQuasi G Player.one hP).1.IsWinning := by
  dsimp [IsWinning]; rw [waiting_equals_pre hP h' (p := Player.one)]
  exact waiting_winning_isOpen h hP

end GaleStewartGame.Game