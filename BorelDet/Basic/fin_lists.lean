import BorelDet.Basic.general

variable {α β γ : Type*} {a : α} {m n : ℕ}

namespace List
variable (x y z : List α)
/-@[congr] lemma congr_get (m : Fin x.length) (h : x = y) : -not needed anymore with List.getElem?
  x.get m = y.get ⟨m.val, h ▸ m.prop⟩ := h ▸ rfl
--this does still work, so does simp backtrack?
example (x : List α) {n m} (h : n = m) : x.get n = x.get m := by simp [h]-/

@[simp] lemma take_eq_self n :
  x.take n = x ↔ x.length ≤ n := by
  constructor
  · intro h; rw [← h]; simp
  · exact take_of_length_le
@[simp] lemma take_self_eq n :
  x = x.take n ↔ x.length ≤ n := by
  rw [Eq.comm, take_eq_self]
@[simp] lemma take_eq_left n :
  (x ++ y).take n = x.take n ↔ y = [] ∨ n ≤ x.length := by
  constructor
  · rcases le_or_gt n x.length with _ | h
    · tauto
    · cases y
      · tauto
      · intro h; apply_fun length at h; simp at h; omega
  · rintro (rfl | h)
    · rw [append_nil]
    · exact take_append_of_le_length h
@[simp] lemma take_eq_right n :
  x.take n = (x ++ y).take n ↔ y = [] ∨ n ≤ x.length := by
  rw [Eq.comm]; apply take_eq_left
@[simp] lemma drop_take_append_drop {α : Type*} (x : List α) (m n : ℕ) :
  (x.drop m).take n ++ x.drop (n + m) = x.drop m := by rw [← drop_drop, take_append_drop]
@[simp] lemma drop_take_append_drop' {α : Type*} (x : List α) (m n : ℕ) :
  (x.drop m).take n ++ x.drop (m + n) = x.drop m := by rw [add_comm, drop_take_append_drop]
theorem get?_append_or_none (n : ℕ) :
  x[n]? = (x ++ y)[n]? ∨ x[n]? = none := by
  rcases lt_or_ge n x.length with h | h <;> simp [getElem?_append, get?_eq_none, h]
lemma IsPrefix.take {x y : List α} (h : x <+: y) n : x.take n <+: y.take n := by
  simpa [prefix_take_iff] using IsPrefix.trans (take_prefix n x) h
lemma IsPrefix.drop {x y : List α} (h : x <+: y) n : x.drop n <+: y.drop n := by
  rw [prefix_iff_eq_take.mp h, drop_take]; apply take_prefix
lemma isPrefix_append_of_length (h : x.length ≤ y.length) :
  x <+: y ++ z ↔ x <+: y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.trans <| y.prefix_append z⟩
  rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left]; tauto
@[simp] lemma take_prefix_take :
  x.take m <+: x.take n ↔ m ≤ n ∨ x.length ≤ n := by --see take eq take
  simp [List.prefix_take_iff, List.take_prefix]
@[simp] lemma take_concat_get' (l : List α) (i : ℕ) (h : i < l.length) :
  l.take i ++ [l[i]] = l.take (i + 1) := by
  rw [← concat_eq_append]; exact take_concat_get l i h
lemma get_map' (f: α → β) (x : List α) (n : ℕ) (h : n < x.length) :
  (x.map f)[n]'(by simpa) = f x[n] := getElem_map f
theorem eq_take_concat (x : List α) n (h : x.length = n + 1) :
  x = x.take n ++ [x[n]] := by
  rw [take_concat_get', ← h, take_length]
lemma head_eq_get (x : List α) h : x.head h = x[0]'(List.length_pos.mpr h) :=
  (getElem_zero (List.length_pos.mpr h)).symm
lemma tail_eq_drop : ∀ x : List α, x.tail = x.drop 1
  | [] => by simp
  | _ :: _ => by simp
lemma tail_take : (x.take (n + 1)).tail = x.tail.take n := by
  cases x <;> simp
lemma head_tail_take (x : List α) h : x.head h :: x.tail.take n = x.take (n + 1) := by
  cases x <;> simp at h ⊢
lemma tail_get (x : List α) n (h : n < x.tail.length) :
  x.tail[n] = x[n + 1]'(by abstract simp at h; omega) := by
  simp_rw [tail_eq_drop, getElem_drop, add_comm]
lemma zipWith_left : ∀ (x : List α) (z : List β), List.zipWith (fun a _ ↦ a) x z = x.take z.length
  | [], _ => by simp
  | _, [] => by simp
  | x :: xs, z :: zs => by simpa [zipWith_cons_cons] using zipWith_left xs zs
lemma map_inits (g : α → β) : (x.map g).inits = x.inits.map (map g) := by
  induction' x using reverseRecOn <;> simp [*]
lemma inits_take : (x.take n).inits = x.inits.take (n + 1) := by
  apply List.ext_getElem <;> (simp only [length_inits, length_take, getElem_inits,
    take_take, getElem_take, take_eq_take]; omega)
theorem eq_nil_or_append (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  simpa using l.eq_nil_or_concat
end List

abbrev eval (a : α) {β: α → Type*} (f : ∀ a, β a) := f a
namespace List
abbrev mapEval {α: Type*} {β: α → Type*} (a : α) (x : List (∀ a, β a)) := x.map (eval a)
def zipFun {α: Type*} {β: α → Type*} {n : ℕ} (f : (a : α) → List (β a))
  (h : ∀ a, (f a).length = n) :
   List ((a : α) → β a) := match n with
  | 0 => []
  | n + 1 => (fun a ↦ (f a).head (ne_nil_of_length_eq_add_one (h a)))
    :: zipFun (fun a ↦ (f a).tail) ((by simp [h]) : ∀ a, length _ = n)
@[simp] theorem mapEval_zip {β: α → Type*} (f : (a : α) → List (β a)) (h : ∀ a, (f a).length = n) :
 (zipFun f h).mapEval a = f a := by
  induction' n with n ih generalizing f
  · specialize h a; simp at h; simp [zipFun, h]
  · simp [zipFun, ih]
@[simp] theorem zip_mapEval {β: α → Type*} (x : List ((a : α) → β a)) :
  zipFun x.mapEval (n := x.length) (by simp) = x := by induction' x <;> simp [zipFun, *]
theorem mapEval_joint_epi {β: α → Type*} {x y : List (∀ a, β a)} (hl : x.length = y.length)
  (h : ∀ a, x.mapEval a = y.mapEval a) : x = y := by
  rw [← zip_mapEval x, ← zip_mapEval y]; simp_rw [hl, h]
@[simp, simp_lengths] theorem zipFun_len {β: α → Type*} (f : (a : α) → List (β a))
  (h : ∀ a, (f a).length = n) : (zipFun f h).length (α := no_index _) = n := by
  induction' n with _ ih generalizing f <;> simp [zipFun, *]
@[simp] theorem zipFun_zero {β: α → Type*} (f : (a : α) → List (β a)) (h : ∀ a, (f a).length = 0) :
  zipFun f h = [] := by apply eq_nil_of_length_eq_zero; simp
@[simp] theorem zipFun_append {β: α → Type*} (f g : (a : α) → List (β a))
  (hf : ∀ a, (f a).length = m) (hg : ∀ a, (g a).length = n) :
  zipFun f hf ++ zipFun g hg = zipFun (n := m + n) (fun a ↦ f a ++ g a) (by simp [hf, hg]) := by
  induction' m with m ih generalizing f
  · simp [eq_nil_of_length_eq_zero (hf _)]
  · have hf' a : f a ≠ [] := by intro h; simpa [h] using hf a
    simp [zipFun, Nat.succ_add, ih, tail_append_of_ne_nil, hf']
@[gcongr] theorem zipFun_mono {β: α → Type*} (f g : (a : α) → List (β a))
  (hf : ∀ a, (f a).length = m) (hg : ∀ a, (g a).length = n) (hm : m ≤ n) (h : ∀ a, f a <+: g a) :
  zipFun f hf <+: zipFun g hg := by
  use zipFun (n := n-m) (fun a ↦ drop m (g a)) (by simp [hg])
  simp [hm]; congr; ext a; nth_rw 2 [← take_append_drop m (g a)]
  rw [← hf a, ← prefix_iff_eq_take.mp (h a)]

variable (x y : List α) (a : α) (f : α → List α → β)
def zipInitsMap := x.zipWith f x.inits.tail
@[simp] lemma zipInitsMap_nil : [].zipInitsMap f = [] := by simp [zipInitsMap]
@[simp] lemma zipInitsMap_singleton : [a].zipInitsMap f = [f a [a]] := rfl
lemma zipInitsMap_append : (x ++ y).zipInitsMap f
  = x.zipInitsMap f ++ y.zipInitsMap (fun a z ↦ f a (x ++ z)) := by
  have h : ¬ x.inits.isEmpty := by rw [List.isEmpty_iff_length_eq_zero]; simp
  simp [zipInitsMap, tail_append, h, zipWith_append, ← map_tail, zipWith_map_right]
lemma IsPrefix.zipInitsMap (h : x <+: y) : x.zipInitsMap f <+: y.zipInitsMap f := by
  obtain ⟨_, rfl⟩ := h; rw [zipInitsMap_append]; constructor; rfl
@[simp] lemma zipInitsMap_concat : (x ++ [a]).zipInitsMap f = x.zipInitsMap f ++ [f a (x ++ [a])] := by
  simp [zipInitsMap_append]
@[simp, simp_lengths] lemma zipInitsMap_length :
  (x.zipInitsMap f).length (α := no_index _) = x.length := by simp [zipInitsMap]
lemma zipInitsMap_take : (x.zipInitsMap f).take n = (x.take n).zipInitsMap f := by
  simp [zipInitsMap, take_zipWith, inits_take, tail_take]
lemma map_zipInitsMap (f : α → β) (g : β → List β → γ) :
  x.zipInitsMap (fun a y ↦ g (f a) (y.map f)) = (x.map f).zipInitsMap g := by
  simp [zipInitsMap, map_inits, ← map_tail]
lemma zipInitsMap_map (g : β → γ) :
  x.zipInitsMap (fun a b ↦ g (f a b)) = (x.zipInitsMap f).map g := by
  simp [zipInitsMap, map_zipWith]
@[simp] lemma zipInitsMap_eq_map (g : α → β) :
  x.zipInitsMap (fun a _ ↦ g a) = x.map g := by
  simp [zipInitsMap, ← map_zipWith, zipWith_left]
@[simp] lemma zipInitsMap_get n (h : n < (x.zipInitsMap f).length) : (x.zipInitsMap f)[n]
  = f (x[n]'(by simpa using h)) (x.take (n + 1)) := by
  simp [zipInitsMap, tail_get]

end List
