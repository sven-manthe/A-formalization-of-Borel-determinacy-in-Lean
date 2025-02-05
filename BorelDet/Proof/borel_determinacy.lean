import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BorelDet.Proof.Zero.strat
import BorelDet.Proof.One.strat
import BorelDet.Proof.covering_lim

namespace GaleStewartGame
open Descriptive Tree Covering Stream'.Discrete
open Classical MeasureTheory CategoryTheory
noncomputable section

namespace BorelDet
variable {A : Type*} {G : Game A} {k : ℕ} (hyp : Hyp G k)
abbrev Gh : Games := ⟨A, G, hyp.pruned, hyp.nonempty⟩
abbrev G'h : Games := ⟨A', G', gameTree_isPruned, gameTree_ne⟩
def treeCov : (G'h hyp).tree ⟶ (Gh hyp).tree where
  toHom := π
  str := {
    toFun := by rintro (_ | _) <;> [apply Zero.stratMap; apply One.stratMap]
    con := by rintro (_ | _) _ _ _ _ <;> rfl
  }
  h_body := by rintro (_ | _); apply Zero.body_stratMap; apply One.body_stratMap
def gameCov : Games.Covering (G'h hyp) (Gh hyp) where
  toCovering := treeCov hyp
  hpre := game_payoff hyp
lemma main_lemma {G : Games} (hC : IsClosed G.2.1.payoff) : G.IsUnravelable :=
  fun k ↦ ⟨G'h (k := k) ⟨hC, G.2.2.1, G.2.2.2⟩, gameCov _, by
    unfold gameCov treeCov; use by synth_fixing
    rintro (_ | _) <;> (ext; dsimp only [Zero.stratMap, One.stratMap]) <;>
      (split_ifs <;> ((try omega) <;> rfl)), payoff_clopen⟩
end BorelDet
namespace BorelDet'

variable (T : PTrees) (W : Set (body T.1.2)) {n : ℕ}
@[simps] def extendToGame : Games where
  fst := T.1.1
  snd := {
    fst := {
      tree := T.1.2
      payoff := W
    }
    snd := T.2
  }

/-- a slight strengthening of Martin's notion of unravelable games to facilitate Borel induction -/
def UniversallyUnravelable :=
  ∀ ⦃T'⦄ (f : T' ⟶ T), (extendToGame T' <| (bodyFunctor.map f.toHom)⁻¹' W).IsUnravelable
lemma unravelable_complement (h : UniversallyUnravelable T W) :
  UniversallyUnravelable T Wᶜ := by
  intro _ f n; obtain ⟨G, f, ht, hc⟩ := h f n
  use extendToGame G.tree (Subtype.val⁻¹' G.2.1.payoff)ᶜ
  use { toCovering := f.toCovering, hpre := (by
    simp [Set.compl_eq_univ_diff]; rw [← f.hpre]; rfl) }, ht
  simpa [Set.compl_eq_univ_diff] using hc.compl
lemma closed_unravelable (h : IsClosed W) : UniversallyUnravelable T W := by
  intro T' f; apply BorelDet.main_lemma
  simpa using h.preimage (LenHom.bodyMap_continuous f.toHom)
lemma open_unravelable (h : IsOpen W) : UniversallyUnravelable T W := by
  rw [← compl_compl W]; apply unravelable_complement; apply closed_unravelable
  exact isClosed_compl_iff.mpr h
lemma unravelable_preimage {T' T : PTrees} (f : T' ⟶ T) W (h : UniversallyUnravelable T W) :
  UniversallyUnravelable T' ((bodyFunctor.map f.toHom)⁻¹' W) := by
  intro _ g; simpa using h (g ≫ f)

structure PartiallyUnravelled (n : ℕ) where
  carrier : PTrees
  sets : ℕ → PSigma (UniversallyUnravelable carrier)
  unrav : ∀ m < n, IsOpen (sets m).1
def PartiallyUnravelled.continue (G : PartiallyUnravelled n) (k : ℕ) :
  Σ' (G' : PartiallyUnravelled (n + 1)) (f : G'.carrier ⟶ G.carrier),
  Covering.Fixing (k + n) f ∧
  ∀ n, (G'.sets n).1 = (bodyFunctor.map f.toHom)⁻¹' (G.sets n).1 := by
  apply choice
  have ⟨car, ⟨f, ⟨hf, h⟩⟩⟩ := (G.sets n).2 (𝟙 G.carrier) (k + n)
  constructor
  use {
    carrier := car.tree
    sets := fun n ↦ ⟨(bodyFunctor.map f.toHom)⁻¹' (G.sets n).1,
      unravelable_preimage _ _ (G.sets n).2⟩
    unrav := by
      intro m hm; rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact (G.unrav m hm).preimage (LenHom.bodyMap_continuous f.toHom)
      · have hf := f.hpre
        simp_rw [← bodyFunctor_obj, id_covering_toHom, extendToGame,
          CategoryTheory.Functor.map_id, bodyFunctor_obj, cat_preimage_id] at hf
        simpa only [hf] using h.isOpen
  }, f.toCovering, hf, fun _ ↦ rfl
variable (G : PartiallyUnravelled 0) (k : ℕ)
def unravel_nth : ∀ n, PartiallyUnravelled n
  | 0 => G
  | n + 1 => ((unravel_nth n).continue k).1
def unravelFunctor : ℕᵒᵖ ⥤ PTrees :=
  nat_free_cat.symm ⟨fun n ↦ (unravel_nth G k n).carrier,
    fun n ↦ ((unravel_nth G k n).continue k).2.1⟩
lemma unravelFunctor_succ n :
  (unravelFunctor G k).map (homOfLE (Nat.le_succ n)).op
    = ((unravel_nth G k n).continue k).2.1 := by
  show (nat_free_cat (unravelFunctor G k)).2 _ = _
  simp [unravelFunctor]
lemma unravelFunctor_fixing n :
  Covering.Fixing (k + n) ((unravelFunctor G k).map (homOfLE (Nat.le_succ n)).op) := by
  simpa [unravelFunctor_succ] using ((unravel_nth G k n).continue k).2.2.1
lemma unravelFunctor_preimage m n :
  (Tree.bodyFunctor.map
    ((unravelFunctor G k).map (homOfLE (by simp : 0 ≤ n)).op).toHom)⁻¹' (G.sets m).1
  = ((unravel_nth G k n).sets m).1 := by
  induction' n with n ih
  · simp [unravel_nth]
  · have : (homOfLE (by simp : 0 ≤ n + 1)).op
      = (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (by simp : 0 ≤ n)).op :=
      by apply Subsingleton.elim
    simp [*, unravelFunctor_succ, ← ((unravel_nth G k n).continue k).2.2.2, unravel_nth]
def unravelLim : Limits.Cone (unravelFunctor G k) :=
  limCone (unravelFunctor_fixing G k)
lemma unravelLim_fixing : Covering.Fixing k ((unravelLim G k).π.app ⟨0⟩) :=
  limCone_fixing (unravelFunctor_fixing G k) 0

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- the σ-algebra of universally unravelable sets -/
def unravelableAsMeasurable : MeasurableSpace (Tree.body T.1.2) where
  MeasurableSet' := UniversallyUnravelable T
  measurableSet_empty := open_unravelable T ∅ isOpen_empty
  measurableSet_compl := unravelable_complement T
  measurableSet_iUnion := by
    intro W hW T' f k
    let G0: PartiallyUnravelled 0 := {
      carrier := T'
      sets := fun n ↦ ⟨(Tree.bodyFunctor.map f.toHom)⁻¹' (W n), unravelable_preimage _ _ (hW n)⟩
      unrav := by simp --since mathlib update, inference of DiscreteTopology here is slow
    }
    let F := unravelFunctor G0 k
    let G := (unravelLim G0 k).pt; let π := (unravelLim G0 k).π
    have hO : IsOpen ((Tree.bodyFunctor.map (π.app ⟨0⟩).toHom)⁻¹'
      ((Tree.bodyFunctor.map f.toHom)⁻¹' (⋃i, W i))) := by
      simp_rw [Set.preimage_iUnion]; apply isOpen_iUnion; intro n
      have hnat : π.app ⟨0⟩ = π.app ⟨n + 1⟩ ≫ F.map (homOfLE (by omega)).op := by
        rw [Limits.Cone.w]
      simp_rw [hnat, comp_covering_toHom, Functor.map_comp, cat_preimage_comp]
      erw [unravelFunctor_preimage]
      exact ((unravel_nth G0 k (n + 1)).unrav n (by omega)).preimage
        (Tree.LenHom.bodyMap_continuous _)
    obtain ⟨G', g, hgT, _⟩ := open_unravelable _ _ hO (𝟙 _) k
    let gc : G'.tree ⟶ G := g.toCovering
    use G', {
      toCovering := gc ≫ π.app ⟨0⟩
      hpre := by rw [← g.hpre]; simp [gc]
    }, fixing_comp k gc _ hgT <| unravelLim_fixing G0 k

lemma borel_unravelable : borel _ ≤ unravelableAsMeasurable T :=
  MeasurableSpace.generateFrom_le <| open_unravelable T
end BorelDet'

/-- Borel games are determined -/
lemma Games.borel_determinacy (G : Games) (h : MeasurableSet[borel _] G.2.1.payoff) :
  G.2.1.IsDetermined := by
  simpa [BorelDet'.extendToGame] using
    (BorelDet'.borel_unravelable G.tree _ h (𝟙 G.tree)).isDetermined
theorem borel_determinacy {A : Type*} {G : Game A}
  (hB : MeasurableSet[borel _] G.payoff) (hP : Tree.IsPruned G.tree) : G.IsDetermined := by
  by_cases h : [] ∈ G.tree
  · exact Games.borel_determinacy ⟨A, G, hP, h⟩ hB
  · rw [G.empty_of_tree (by simpa)]
    exact ⟨Player.zero, PreStrategy.existsWinning_empty⟩

end
end GaleStewartGame
