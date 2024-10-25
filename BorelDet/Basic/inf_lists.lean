import Mathlib.Topology.Basic
import BorelDet.Basic.fin_lists

variable {A B : Type*} (m n : ℕ) (a b : ℕ → A) (x y : List A)
--compare PiNat, CantorScheme

namespace InfList
section
variable (a : A) (as : ℕ → A)
def cons : ℕ → A := fun n => match n with
  | 0 => a
  | n + 1 => as n
@[simp] theorem cons_zero : cons a as 0 = a := rfl
@[simp] theorem cons_succ : cons a as (n + 1) = as n := rfl
def appendInf : ℕ → A := x.foldr cons as
instance : HAppend (List A) (ℕ → A) (ℕ → A) where hAppend := appendInf
@[simp] theorem nil_append : ([]: List A) ++ as = as := rfl
@[simp] theorem cons_append : (a :: x) ++ as = cons a (x ++ as) := rfl
@[simp] theorem append_assoc : x ++ y ++ as = x ++ (y ++ as) := List.foldr_append _ _ _ _
theorem append_eq_cons : [a] ++ as = cons a as := by dsimp
theorem append_cons : x ++ cons a as = x ++ [a] ++ as := by simp

def tail : ℕ → A := (as ∘ (· + 1))
@[simp] theorem eval_tail_one : (tail as) n = as (n + 1) := rfl
@[simp] theorem eval_tail : (tail^[m] as) n = as (m + n) := by
  induction' m with m ih generalizing as
  · simp
  · rw [Function.iterate_succ, Function.comp_apply, ih (tail as), Nat.succ_add]; rfl
@[simp] theorem tail_cons : tail (cons a as) = as := rfl
@[simp] theorem cons_tail : cons (as 0) (tail as) = as := by
  ext n; cases n <;> rfl
end

variable {x y a b n}
theorem eval_append_left (h : n < x.length) :
  (x ++ a) n = x[n]? := by
  induction' x with b x ih generalizing n
  · simp at h
  · rcases n with (_ | n)
    · simp
    · rw [List.length_cons, Nat.succ_lt_succ_iff] at h; simp [ih h]
theorem eval_append_left' (h : n < x.length) :
  (x ++ a) n = x[n] := by
  apply Option.some_injective; rw [← List.getElem?_eq_getElem]; exact eval_append_left h
variable (x y a b n)
@[simp] theorem eval_append_right : (x ++ a) (x.length + n) = a n := by
  induction' x <;> simp [Nat.succ_add, *]
@[simp] theorem eval_append0 : (x ++ a) x.length = a 0 :=
  eval_append_right 0 _ _
@[simp] theorem reduce_append : x ++ a = x ++ b ↔ a = b := by
  constructor <;> intro h
  · ext n; simpa using congr_fun h (x.length + n)
  · rw [h]
@[simp] theorem eval_append_zero {a : A} {as : ℕ → A} : (a :: x ++ as) 0 = a := rfl
theorem append_reduce
  (h : x ++ a = y ++ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl; intros
  rw [← eval_append_left', ← eval_append_left', h]
@[simp] lemma map_append (f : A → B) : f ∘ (x ++ a) = x.map f ++ f ∘ a := by
  ext n; rcases lt_or_ge n x.length with h | h
  · simp [eval_append_left' h, eval_append_left' (by simpa : n < (x.map f).length)]
  · obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h
    nth_rw 2 [← x.length_map f]; simp only [Function.comp_apply, eval_append_right]

def _root_.Function.take : ℕ → (ℕ → A) → List A
  | 0, _ => []
  | n + 1, a => a 0 :: take n (tail a)
@[simp] theorem take_zero : a.take 0 = [] := rfl
theorem take_succ : a.take (n + 1) = a 0 :: (tail a).take n := rfl
@[simp, simp_lengths] theorem take_length : (a.take n).length = n := by
  induction' n generalizing a <;> simp [Function.take, *]
@[simp] theorem take_append : a.take n ++ tail^[n] a = a := by
  induction' n with n ih generalizing a <;> simp [take_succ, *]
theorem append_take (x : List A) (a : ℕ →  A) (n : ℕ) :
  x ++ (a.take n) = (x ++ a).take (x.length + n) := by
  induction' x <;> simp [Function.take, add_comm, *]
@[simp] theorem take_eval {a : ℕ → A} {m n : ℕ} (h : m < n) : (a.take n)[m]? = a m := by
  nth_rw 2 [← take_append n a]; rw [eval_append_left]; simp [h]
@[simp] theorem take_eval' {a : ℕ → A} n m (h : m < (a.take n).length) :
  (a.take n)[m] = a m := by
  apply Option.some_injective; rw [← take_eval]; symm; apply List.getElem?_eq_getElem
  simpa using h
theorem take_append_of_le_length (x : List A) (a : ℕ → A) {n : ℕ} (h : n ≤ x.length) :
  (x ++ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro m hm _; simp at hm
  rw [List.getElem_take, take_eval', eval_append_left']
theorem take_add (m n : ℕ) : (a.take (m + n)) = (a.take m) ++ ((tail^[m] a).take n) := by
  apply append_reduce (tail^[m + n] a) (tail^[n] (tail^[m] a)) <;> simp [take_append]
theorem take_succ' (n : ℕ) : (a.take (n + 1)) = (a.take n) ++ [a n] := by
  rw [take_add]; simp [take_succ]
@[simp] theorem take_take : (a.take n).take m = a.take (min m n) := by
  rcases le_total m n with h | h
  · apply List.ext_getElem <;> simp [h, List.getElem_take']
  · simp [h, List.take_of_length_le]
@[simp] theorem take_prefix : a.take m <+: a.take n ↔ m ≤ n := by
  constructor <;> intro h
  · simpa using h.length_le
  · have h' : a.take m = (a.take n).take m := by simp [h]
    rw [h']; apply List.take_prefix
lemma map_take (f : A → B) : (a.take n).map f = (f ∘ a).take n := by
  apply List.ext_getElem <;> simp
lemma take_drop : (tail^[m] a).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp (config := {contextual := true}) [← List.getElem_drop']
lemma drop_append_of_le_length (x : List A) (a : ℕ → A) {n : ℕ} (h : n ≤ x.length) :
  tail^[n] (x ++ a) = x.drop n ++ a := by
  obtain ⟨m, hm⟩ := le_iff_exists_add.mp h
  ext k; by_cases hk : k < m
  · rw [eval_tail, eval_append_left', eval_append_left', List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := le_iff_exists_add.mp (by simpa using hk)
    have : m = (x.drop n).length := by simp [hm]
    simp [← add_assoc, ← hm]; rw [this, eval_append_right]

@[simp] lemma append_compose (x y : List A) : (x ++ ·) ∘ (y ++ ·) = ((x ++ y) ++ ·) := by
  ext1; simp [List.append_assoc]
@[simp] lemma append_inf_compose (x y : List A) :
  (x ++ · : (ℕ → A) → ℕ → A) ∘ (y ++ · : (ℕ → A) → ℕ → A) = ((x ++ y) ++ · : (ℕ → A) → ℕ → A) := by
  ext1; simp [append_assoc]
@[simp] lemma subAtFin_append (T : Set (List A)) (x y : List A) :
  (y ++ ·)⁻¹' ((x ++ ·)⁻¹' T) = ((x ++ y) ++ ·)⁻¹' T := by
  simp [← Set.preimage_comp]
@[simp] lemma subAtInf_append (T : Set (ℕ → A)) (x y : List A) :
  (y ++ · : (ℕ → A) → ℕ → A)⁻¹' ((x ++ · : (ℕ → A) → ℕ → A)⁻¹' T)
  = ((x ++ y) ++ · : (ℕ → A) → ℕ → A )⁻¹' T := by
  simp [← Set.preimage_comp]

def basicOpen : Set (ℕ → A) := Set.range (x ++ · : (ℕ → A) → (ℕ → A))
@[simp] theorem basicOpen_nil : @basicOpen A [] = Set.univ := by simp [basicOpen]
@[simp] theorem basicOpen_append :
  x ++ a ∈ basicOpen (x ++ y) ↔ a ∈ basicOpen y := by simp [basicOpen]
@[simp] theorem basicOpen_append_nil (x : List A) (a : ℕ → A) : x ++ a ∈ basicOpen x := by
  simpa using basicOpen_append a x []
@[simp] theorem basicOpen_cons_nil (a : A) (as : ℕ → A) : cons a as ∈ basicOpen [a] := by
  apply basicOpen_append_nil
@[simp] theorem extend_sub : a ∈ basicOpen (a.take n) := by
  use tail^[n] a; simp
theorem basicOpen_iff_restrict {a : ℕ → A} {x : List A} :
  a ∈ basicOpen x ↔ x = a.take x.length := by
  constructor
  · rintro ⟨b, _, rfl⟩; simp [take_append_of_le_length]
  · rintro h; rw [h]; exact extend_sub _ _
theorem basicOpen_cons {as : ℕ → A} {x : List A} {a : A} :
  as ∈ basicOpen (a :: x) ↔ as 0 = a ∧ tail as ∈ basicOpen x := by
  simp [basicOpen]; nth_rw 1 [← exists_and_left, ← cons_tail as]; congr!
  constructor <;> simp (config := { contextual := true })
  exact fun h ↦ ⟨(congr_fun h 0).symm, funext fun n ↦ congr_fun h (n + 1)⟩
theorem basicOpen_index {a : ℕ → A} (x : List A) :
  a ∈ basicOpen x ↔ ∀ n < x.length, a n = x[n]? := by
  rw [basicOpen_iff_restrict]; constructor <;> intro h
  · intro n h'; rw [h, take_eval h']
  · symm; apply List.ext_get?'; intro n h'; simp at h' ⊢; rw [← h n h', take_eval h']
theorem basicOpen_concat {as : ℕ → A} {x : List A} {a : A} :
  as ∈ basicOpen (x ++ [a]) ↔ as ∈ basicOpen x ∧ as x.length = a := by
  induction' x with x xs ih generalizing as
  · simp [basicOpen_cons]
  · simp [basicOpen_cons, @ih (tail as), and_assoc]
theorem basicOpen_restrict : a ∈ basicOpen (b.take n) ↔ ∀ m < n, a m = b m := by
  rw [basicOpen_index]; simp (config := {contextual := true})
@[simp] theorem basicOpen_sub : basicOpen (x ++ y) ⊆ basicOpen x := by
  intro _ ⟨z, h⟩; use y ++ z; dsimp only; rwa [← append_assoc]
@[gcongr] theorem basicOpen_mono {x y : List A} (h : x <+: y) : basicOpen y ⊆ basicOpen x := by
  obtain ⟨z, rfl⟩ := h; apply basicOpen_sub

theorem basicOpen_complement : (basicOpen x)ᶜ
  = ⋃ y, ⋃ (_: x.length = y.length ∧ x ≠ y), basicOpen y := by
  ext a; constructor <;> simp only [Set.mem_iUnion]
  · intro h; use a.take x.length
    simp; intro h'; apply h; rw [h']; simp
  · intro ⟨x', ⟨hl, hne⟩, ⟨a1, h1⟩⟩ ⟨a2, h2⟩
    apply hne; apply append_reduce; dsimp at h1 h2; rwa [h1, h2]
variable [TopologicalSpace A]
theorem tail_con : Continuous (@tail A) := continuous_pi fun i ↦ continuous_apply (i + 1)
theorem append_con : Continuous ((x ++ ·) : (ℕ → A) → ℕ → A) := by
  apply continuous_pi; intro i; rcases lt_or_ge i x.length with h | h
  simp_rw [eval_append_left' h]; exact continuous_const
  obtain ⟨i, rfl⟩ := le_iff_exists_add.mp h; simp_rw [eval_append_right]; exact continuous_apply i
variable  [DiscreteTopology A]
theorem hasBasis_basicOpen : (nhds a).HasBasis
  (fun x ↦ a ∈ basicOpen x) (fun x ↦ basicOpen x) := by
  rw [nhds_pi, nhds_discrete]; apply Filter.HasBasis.to_hasBasis
  · apply Filter.hasBasis_pi; intro _; apply Filter.hasBasis_pure
  · intro ⟨I, _⟩ ⟨fin, _⟩; have ⟨N, hN⟩ := fin.bddAbove
    refine ⟨a.take (N + 1), extend_sub _ _, fun b hb n hn ↦ ?_⟩
    rw [basicOpen_restrict] at hb
    exact hb n <| lt_of_le_of_lt (hN hn) (Nat.lt_succ_self _)
  · rintro x ⟨a, _, rfl⟩
    refine ⟨⟨Finset.range x.length, fun _ ↦ ()⟩,
      ⟨Set.toFinite _, fun _ _ ↦ trivial⟩, fun b hb ↦ ?_⟩
    rw [basicOpen_index]; intro n hn
    rw [hb n (by simp [hn]), eval_append_left hn]
theorem hasBasis_basicOpen': (nhds a).HasBasis
  (fun n ↦ n ≥ m) (fun n ↦ basicOpen (a.take n)) := by
  apply Filter.HasBasis.to_hasBasis (hasBasis_basicOpen a)
  · intro x hx; rw [basicOpen_iff_restrict] at hx; rw [hx]
    use m + x.length; simp [basicOpen_mono]
  · intro n _; use a.take n; simp
@[simp] theorem basicOpen_isOpen : IsOpen (basicOpen x) :=
  isOpen_iff_mem_nhds.mpr fun a h ↦ (hasBasis_basicOpen a).mem_iff.mpr ⟨x, h, subset_rfl⟩
@[simp] theorem basicOpen_isClosed : IsClosed (basicOpen x) := by
  rw [← isOpen_compl_iff, basicOpen_complement]
  exact isOpen_biUnion fun i _ ↦ basicOpen_isOpen i
end InfList
