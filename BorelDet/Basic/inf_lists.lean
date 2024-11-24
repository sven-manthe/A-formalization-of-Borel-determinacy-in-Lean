import Mathlib.Topology.Basic
import Mathlib.Data.Stream.Init
import BorelDet.Basic.fin_lists

namespace Stream'
variable {A B : Type*} (f : A → B) (m n : ℕ) (a b : Stream' A) (x y : List A)

attribute [simp] nil_append_stream append_append_stream append_stream_head_tail
@[simp] lemma eval_cons_append_zero {a : A} {as : Stream' A} : (a :: x ++ₛ as).get 0 = a := rfl
@[simp] lemma cons_head_tail : a.tail.cons a.head = a := by
  ext n; cases n <;> rfl
@[simp] lemma append_eq_cons {a : A} {as : Stream' A} : [a] ++ₛ as = a :: as := by rfl
lemma get_append_left (h : n < x.length) : (x ++ₛ a).get n = x[n] := by
  induction' x with b x ih generalizing n
  · simp at h
  · rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]
@[simp] lemma get_append_right : (x ++ₛ a).get (x.length + n) = a.get n := by
  induction' x <;> simp [Nat.succ_add, *, cons_append_stream]
@[simp] lemma get_append_zero : (x ++ₛ a).get x.length = a.get 0 := get_append_right 0 a x
lemma append_left_injective (h : x ++ₛ a = x ++ₛ b) : a = b := by
  ext n; apply_fun fun a ↦ a.get (x.length + n) at h; simpa using h
@[simp] lemma append_left_inj : x ++ₛ a = x ++ₛ b ↔ a = b :=
  ⟨append_left_injective a b x, by simp (config := {contextual := true})⟩
lemma append_right_injective (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left, ← get_append_left, h]
lemma append_take : x ++ (a.take n) = (x ++ₛ a).take (x.length + n) := by
  induction' x <;> simp [take, add_comm, cons_append_stream, *]
@[simp] lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a.get m := by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]
theorem take_append_of_le_length (x : List A) (a : Stream' A) {n : ℕ} (h : n ≤ x.length) :
  (x ++ₛ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]
lemma take_add : a.take (m + n) = a.take m ++ (a.drop m).take n := by
  apply append_right_injective (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [- drop_drop]
@[gcongr] lemma take_prefix_take_left (h : m ≤ n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix
@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
  ⟨fun h ↦ by simpa using h.length_le, take_prefix_take_left m n a⟩
lemma map_take : (a.take n).map f = (a.map f).take n := by
  apply List.ext_getElem <;> simp

@[simp (1100)] --TODO
theorem get_drop' (n m : ℕ) (s : Stream' A) : get (drop m s) n = get s (m + n) := by
  simp [add_comm]
lemma take_drop : (a.drop m).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp
lemma drop_append_of_le_length (x : List A) (a : Stream' A) {n : ℕ} (h : n ≤ x.length) :
    (x ++ₛ a).drop n = x.drop n ++ₛ a := by
  obtain ⟨m, hm⟩ := le_iff_exists_add.mp h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop', get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := le_iff_exists_add.mp hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop', ← add_assoc, ← hm, get_append_right, hm', get_append_right]

attribute [simp_lengths] Stream'.length_take
--in PR until here
--compare PiNat, CantorScheme

namespace Discrete
@[simp] lemma append_inf_compose (x y : List A) :
  (x ++ₛ ·) ∘ (y ++ₛ ·) = ((x ++ y) ++ₛ ·) := by
  ext1; simp
@[simp] lemma subAtInf_append (T : Set (Stream' A)) (x y : List A) :
  (y ++ₛ ·)⁻¹' ((x ++ₛ ·)⁻¹' T) = ((x ++ y) ++ₛ ·)⁻¹' T := by
  simp [← Set.preimage_comp]

def basicOpen : Set (Stream' A) := Set.range (x ++ₛ ·)
@[simp] theorem basicOpen_nil : @basicOpen A [] = Set.univ := by simp [basicOpen]
@[simp] theorem basicOpen_append :
  x ++ₛ a ∈ basicOpen (x ++ y) ↔ a ∈ basicOpen y := by simp [basicOpen]
@[simp] theorem basicOpen_append_nil : x ++ₛ a ∈ basicOpen x := by
  simpa using basicOpen_append a x []
@[simp] theorem basicOpen_cons_nil (a : A) (as : Stream' A) : as.cons a ∈ basicOpen [a] := by
  apply basicOpen_append_nil
@[simp] theorem extend_sub : a ∈ basicOpen (a.take n) := by
  use a.drop n; simp
theorem basicOpen_iff_restrict : a ∈ basicOpen x ↔ x = a.take x.length := by
  constructor
  · rintro ⟨b, _, rfl⟩; simp [take_append_of_le_length]
  · rintro h; rw [h]; exact extend_sub _ _
theorem basicOpen_cons {as : Stream' A} {x : List A} {a : A} :
  as ∈ basicOpen (a :: x) ↔ as.get 0 = a ∧ tail as ∈ basicOpen x := by
  simp_rw [basicOpen, Set.mem_range]
  nth_rw 1 [← exists_and_left, ← cons_head_tail as]
  simp_rw [cons_append_stream, cons_injective2.eq_iff, Eq.comm]
theorem basicOpen_index : a ∈ basicOpen x ↔ ∀ (n) (_ : n < x.length), a.get n = x[n] := by
  rw [basicOpen_iff_restrict]; constructor <;> intro h
  · intro n h'; simp_rw (config := {singlePass := true}) [h, take_get]
  · symm; apply List.ext_getElem (by simp); simpa using h
theorem basicOpen_concat {as : Stream' A} {x : List A} {a : A} :
  as ∈ basicOpen (x ++ [a]) ↔ as ∈ basicOpen x ∧ as.get x.length = a := by
  induction' x with x xs ih generalizing as
  · simp [basicOpen_cons]
  · simp [basicOpen_cons, @ih (tail as), and_assoc]
theorem basicOpen_restrict : a ∈ basicOpen (b.take n) ↔ ∀ m < n, a.get m = b.get m := by
  rw [basicOpen_index]; simp (config := {contextual := true})
@[simp] theorem basicOpen_sub : basicOpen (x ++ y) ⊆ basicOpen x := by
  intro _ ⟨z, h⟩; use y ++ₛ z; dsimp only; rwa [← append_append_stream]
@[gcongr] theorem basicOpen_mono {x y : List A} (h : x <+: y) : basicOpen y ⊆ basicOpen x := by
  obtain ⟨z, rfl⟩ := h; apply basicOpen_sub

theorem basicOpen_complement : (basicOpen x)ᶜ
  = ⋃ (y) (_ : x.length = y.length ∧ x ≠ y), basicOpen y := by
  ext a; constructor <;> simp only [Set.mem_iUnion]
  · intro h; use a.take x.length
    simp; intro h'; apply h; rw [h']; simp
  · intro ⟨x', ⟨hl, hne⟩, ⟨a1, h1⟩⟩ ⟨a2, h2⟩
    apply hne; apply append_right_injective; dsimp at h1 h2; rwa [h1, h2]
scoped instance prodDisc A : TopologicalSpace (Stream' A) :=
  Pi.topologicalSpace (t₂ := fun _ ↦ ⊥)

section
local instance : TopologicalSpace A := ⊥
local instance : DiscreteTopology A := ⟨rfl⟩
lemma continuous_pi' {X} [TopologicalSpace X] {f : X → Stream' A}
  (h : ∀ i, Continuous fun a => (f a).get i) : Continuous f :=
  continuous_pi_iff.2 h
theorem drop_con : Continuous (@drop A n) := continuous_pi' fun i ↦ continuous_apply (i + n)
theorem tail_con : Continuous (@tail A) := drop_con 1
theorem append_con : Continuous (x ++ₛ ·) := by
  apply continuous_pi'; intro i; rcases lt_or_ge i x.length with h | h
  · simp_rw [get_append_left _ _ _ h]; exact continuous_const
  · obtain ⟨i, rfl⟩ := le_iff_exists_add.mp h
    simpa only [get_append_right] using continuous_apply i
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
    replace hb : b.get n = (x ++ₛ a).get n := hb n (by simp [hn])
    rw [hb, get_append_left _ _ _ hn]
end

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
end Discrete
end Stream'
