import Mathlib.Topology.Basic
import Mathlib.Data.Stream.Init
import BorelDet.Basic.fin_lists

namespace Stream'
attribute [simp_lengths] length_take
variable {A B : Type*} (f : A → B) (m n : ℕ) (a b : Stream' A) (x y : List A)
--compare PiNat, CantorScheme

namespace Discrete
@[simp] lemma append_inf_compose (x y : List A) :
  (x ++ₛ ·) ∘ (y ++ₛ ·) = ((x ++ y) ++ₛ ·) := by
  ext1; simp
@[simp] lemma subAtInf_append (T : Set (Stream' A)) (x y : List A) :
  (y ++ₛ ·)⁻¹' ((x ++ₛ ·)⁻¹' T) = ((x ++ y) ++ₛ ·)⁻¹' T := by
  simp [← Set.preimage_comp]

def principalOpen : Set (Stream' A) := Set.range (x ++ₛ ·)
@[simp] lemma principalOpen_nil : @principalOpen A [] = Set.univ := by simp [principalOpen]
@[simp] lemma principalOpen_append :
  x ++ₛ a ∈ principalOpen (x ++ y) ↔ a ∈ principalOpen y := by simp [principalOpen]
@[simp] lemma principalOpen_append_nil : x ++ₛ a ∈ principalOpen x := by
  simpa using principalOpen_append a x []
@[simp] lemma principalOpen_cons_nil (a : A) (as : Stream' A) : as.cons a ∈ principalOpen [a] := by
  apply principalOpen_append_nil
@[simp] lemma extend_sub : a ∈ principalOpen (a.take n) := by
  use a.drop n; simp
lemma principalOpen_iff_restrict : a ∈ principalOpen x ↔ x = a.take x.length := by
  constructor
  · rintro ⟨b, _, rfl⟩; simp [take_append_of_le_length]
  · rintro h; rw [h]; exact extend_sub _ _
lemma principalOpen_cons {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (a :: x) ↔ as.get 0 = a ∧ tail as ∈ principalOpen x := by
  simp_rw [principalOpen, Set.mem_range]
  nth_rw 1 [← exists_and_left, ← cons_head_tail as]
  simp_rw [cons_append_stream, cons_injective2.eq_iff, Eq.comm]
lemma principalOpen_index : a ∈ principalOpen x ↔ ∀ (n) (_ : n < x.length), a.get n = x[n] := by
  rw [principalOpen_iff_restrict]; constructor <;> intro h
  · intro n h'; simp_rw (config := {singlePass := true}) [h, take_get]
  · symm; apply List.ext_getElem (by simp)
    simp; tauto --simpa using h --fails since mathlib update
lemma principalOpen_concat {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (x ++ [a]) ↔ as ∈ principalOpen x ∧ as.get x.length = a := by
  induction' x with x xs ih generalizing as
  · simp [principalOpen_cons]
  · simp [principalOpen_cons, @ih (tail as), and_assoc]
lemma principalOpen_restrict : a ∈ principalOpen (b.take n) ↔ ∀ m < n, a.get m = b.get m := by
  rw [principalOpen_index]; simp (config := {contextual := true})
@[simp] lemma principalOpen_sub : principalOpen (x ++ y) ⊆ principalOpen x := by
  intro _ ⟨z, h⟩; use y ++ₛ z; dsimp only; rwa [← append_append_stream]
@[gcongr] lemma principalOpen_mono {x y : List A} (h : x <+: y) :
  principalOpen y ⊆ principalOpen x := by obtain ⟨z, rfl⟩ := h; apply principalOpen_sub

lemma principalOpen_complement : (principalOpen x)ᶜ
  = ⋃ (y) (_ : x.length = y.length ∧ x ≠ y), principalOpen y := by
  ext a; constructor <;> simp only [Set.mem_iUnion]
  · intro h; use a.take x.length
    simp; intro h'; apply h; rw [h']; simp
  · intro ⟨x', ⟨hl, hne⟩, ⟨a1, h1⟩⟩ ⟨a2, h2⟩
    apply hne; apply append_left_injective; dsimp at h1 h2; rwa [h1, h2]
scoped instance prodDisc A : TopologicalSpace (Stream' A) :=
  Pi.topologicalSpace (t₂ := fun _ ↦ ⊥)

section
local instance : TopologicalSpace A := ⊥
local instance : DiscreteTopology A := ⟨rfl⟩
lemma continuous_pi' {X} [TopologicalSpace X] {f : X → Stream' A}
  (h : ∀ i, Continuous fun a => (f a).get i) : Continuous f :=
  continuous_pi_iff.2 h
lemma drop_con : Continuous (@drop A n) := continuous_pi' fun i ↦ continuous_apply (i + n)
lemma tail_con : Continuous (@tail A) := drop_con 1
lemma append_con : Continuous (x ++ₛ ·) := by
  apply continuous_pi'; intro i; rcases lt_or_ge i x.length with h | h
  · simp_rw [get_append_left _ _ _ h]; exact continuous_const
  · obtain ⟨i, rfl⟩ := le_iff_exists_add.mp h
    simpa only [get_append_right] using continuous_apply i
lemma hasBasis_principalOpen : (nhds a).HasBasis
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

lemma hasBasis_principalOpen': (nhds a).HasBasis
  (fun n ↦ n ≥ m) (fun n ↦ principalOpen (a.take n)) := by
  apply Filter.HasBasis.to_hasBasis (hasBasis_principalOpen a)
  · intro x hx; rw [principalOpen_iff_restrict] at hx; rw [hx]
    use m + x.length; simp [principalOpen_mono]
  · intro n _; use a.take n; simp
@[simp] lemma principalOpen_isOpen : IsOpen (principalOpen x) :=
  isOpen_iff_mem_nhds.mpr fun a h ↦ (hasBasis_principalOpen a).mem_iff.mpr ⟨x, h, subset_rfl⟩
@[simp] lemma principalOpen_isClosed : IsClosed (principalOpen x) := by
  rw [← isOpen_compl_iff, principalOpen_complement]
  exact isOpen_biUnion fun i _ ↦ principalOpen_isOpen i
end Discrete
end Stream'
