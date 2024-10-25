import Mathlib.Tactic
noncomputable section
def Strategy (T : Set (List ℕ)) := T → ℕ
def Strategy.subtree {T} (S : Strategy T) : Set (List ℕ) := { x | ∀ a y, a = S y }
variable {S T : Set (List ℕ)}
theorem apply_concat (f : S → T) (x : List ℕ) (a : ℕ) :
  ∃ b : ℕ, (f ⟨x ++ [a], sorry⟩).val = [] := by sorry
def fromMap {T : Set (List ℕ)} (f : T → T) (S : Strategy T) : Strategy T := fun x ↦
  (apply_concat f x (S x)).choose
noncomputable def stratMap' {T} (R : Strategy T) : Strategy T :=
  fun x ↦
  if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else if True then (fromMap id) R x
  else (fromMap id) R x

set_option profiler true
structure TreeLift where
  R : Strategy T
  x : (stratMap' R).subtree
