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

@[simp (1100)]
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

--in PR until here
--compare PiNat, CantorScheme

attribute [simp_lengths] Stream'.length_take

namespace Discrete
@[simp] lemma append_inf_compose (x y : List A) :
  (x ++ₛ ·) ∘ (y ++ₛ ·) = ((x ++ y) ++ₛ ·) := by
  ext1; simp
@[simp] lemma subAtInf_append (T : Set (Stream' A)) (x y : List A) :
  (y ++ₛ ·)⁻¹' ((x ++ₛ ·)⁻¹' T) = ((x ++ y) ++ₛ ·)⁻¹' T := by
  simp [← Set.preimage_comp]

def principalOpen : Set (Stream' A) := Set.range (x ++ₛ ·)
@[simp] theorem principalOpen_nil : @principalOpen A [] = Set.univ := by simp [principalOpen]
@[simp] theorem principalOpen_append :
  x ++ₛ a ∈ principalOpen (x ++ y) ↔ a ∈ principalOpen y := by simp [principalOpen]
@[simp] theorem principalOpen_append_nil : x ++ₛ a ∈ principalOpen x := by
  simpa using principalOpen_append a x []
@[simp] theorem principalOpen_cons_nil (a : A) (as : Stream' A) : as.cons a ∈ principalOpen [a] := by
  apply principalOpen_append_nil
@[simp] theorem extend_sub : a ∈ principalOpen (a.take n) := by
  use a.drop n; simp
theorem principalOpen_iff_restrict : a ∈ principalOpen x ↔ x = a.take x.length := by
  constructor
  · rintro ⟨b, _, rfl⟩; simp [take_append_of_le_length]
  · rintro h; rw [h]; exact extend_sub _ _
theorem principalOpen_cons {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (a :: x) ↔ as.get 0 = a ∧ tail as ∈ principalOpen x := by
  simp_rw [principalOpen, Set.mem_range]
  nth_rw 1 [← exists_and_left, ← cons_head_tail as]
  simp_rw [cons_append_stream, cons_injective2.eq_iff, Eq.comm]
theorem principalOpen_index : a ∈ principalOpen x ↔ ∀ (n) (_ : n < x.length), a.get n = x[n] := by
  rw [principalOpen_iff_restrict]; constructor <;> intro h
  · intro n h'; simp_rw (config := {singlePass := true}) [h, take_get]
  · symm; apply List.ext_getElem (by simp); simpa using h
theorem principalOpen_concat {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (x ++ [a]) ↔ as ∈ principalOpen x ∧ as.get x.length = a := by
  induction' x with x xs ih generalizing as
  · simp [principalOpen_cons]
  · simp [principalOpen_cons, @ih (tail as), and_assoc]
theorem principalOpen_restrict : a ∈ principalOpen (b.take n) ↔ ∀ m < n, a.get m = b.get m := by
  rw [principalOpen_index]; simp (config := {contextual := true})
@[simp] theorem principalOpen_sub : principalOpen (x ++ y) ⊆ principalOpen x := by
  intro _ ⟨z, h⟩; use y ++ₛ z; dsimp only; rwa [← append_append_stream]
@[gcongr] theorem principalOpen_mono {x y : List A} (h : x <+: y) :
  principalOpen y ⊆ principalOpen x := by obtain ⟨z, rfl⟩ := h; apply principalOpen_sub

theorem principalOpen_complement : (principalOpen x)ᶜ
  = ⋃ (y) (_ : x.length = y.length ∧ x ≠ y), principalOpen y := by
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
theorem hasBasis_principalOpen : (nhds a).HasBasis
  (fun x ↦ a ∈ principalOpen x) (fun x ↦ principalOpen x) := by
  rw [nhds_pi, nhds_discrete]; apply Filter.HasBasis.to_hasBasis
  · apply Filter.hasBasis_pi; intro _; apply Filter.hasBasis_pure
  · intro ⟨I, _⟩ ⟨fin, _⟩; have ⟨N, hN⟩ := fin.bddAbove
    refine ⟨a.take (N + 1), extend_sub _ _, fun b hb n hn ↦ ?_⟩
    rw [principalOpen_restrict] at hb
    exact hb n <| lt_of_le_of_lt (hN hn) (Nat.lt_succ_self _)
  · rintro x ⟨a, _, rfl⟩
    refine ⟨⟨Finset.range x.length, fun _ ↦ ()⟩,
      ⟨Set.toFinite _, fun _ _ ↦ trivial⟩, fun b hb ↦ ?_⟩
    rw [principalOpen_index]; intro n hn
    replace hb : b.get n = (x ++ₛ a).get n := hb n (by simp [hn])
    rw [hb, get_append_left _ _ _ hn]
end

theorem hasBasis_principalOpen': (nhds a).HasBasis
  (fun n ↦ n ≥ m) (fun n ↦ principalOpen (a.take n)) := by
  apply Filter.HasBasis.to_hasBasis (hasBasis_principalOpen a)
  · intro x hx; rw [principalOpen_iff_restrict] at hx; rw [hx]
    use m + x.length; simp [principalOpen_mono]
  · intro n _; use a.take n; simp
@[simp] theorem principalOpen_isOpen : IsOpen (principalOpen x) :=
  isOpen_iff_mem_nhds.mpr fun a h ↦ (hasBasis_principalOpen a).mem_iff.mpr ⟨x, h, subset_rfl⟩
@[simp] theorem principalOpen_isClosed : IsClosed (principalOpen x) := by
  rw [← isOpen_compl_iff, principalOpen_complement]
  exact isOpen_biUnion fun i _ ↦ principalOpen_isOpen i
end Discrete
end Stream'
