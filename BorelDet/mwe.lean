import Mathlib.Tactic

section
variable {α : ℕ → Type} {β : ∀ n, α n → Prop}
@[congr] lemma test {m n} (h : m = n) : (∃ a, β m a) ↔ ∃ a, β n a := by
  congr!
lemma rewrite_test {m n} (h : m = n) : (∃ a, β m a) ↔ ∃ a, β n a := by
  simp_rw [h] --simp_rw fails, congr fails, rw succeeds, congr! succeeds
  --with congr lemma simp succeeds, congr fails
end
