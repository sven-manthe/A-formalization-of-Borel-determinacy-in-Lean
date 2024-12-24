import BorelDet.Proof.borel_determinacy
import BorelDet.Game.undetermined

namespace GaleStewartGame
open MeasureTheory
open Stream'.Discrete
theorem borel_determinacy {A : Type*} {G : Game A}
  (hB : MeasurableSet[borel _] G.payoff) (hP : Tree.IsPruned G.tree) : G.IsDetermined := by
  by_cases h : [] ∈ G.tree
  · exact Games.borel_determinacy ⟨A, G, hP, h⟩ hB
  · rw [G.empty_of_tree (by simpa)]
    exact ⟨Player.zero, PreStrategy.existsWinning_empty⟩
end GaleStewartGame
