import BorelDet.Game.games

namespace GaleStewartGame
open Classical Cardinal
open Stream'.Discrete Tree PreStrategy

variable {A : Type*}
/-- the strategy which plays the infinite sequence `a` independent of the opponents' moves -/
def Player.ownTree (p : Player) (a : Stream' A) : Strategy (⊤ : Tree A) p :=
  fun x _ ↦ ⟨a.get (x.val.length / 2), by simp⟩
@[simp] theorem Player.ownTree.mem_body {p} {a x : Stream' A} :
  x ∈ body (ownTree p a).pre.subtree ↔ ∀ n, x.get (2 * n + p.toNat) = a.get n := by
  dsimp [Tree.body]; constructor <;> intro h
  · intro n; specialize h (x.take (2 * n + p.toNat + 1)) (extend_sub _ x)
    rw [Stream'.take_succ'] at h
    have h' := congr_arg Subtype.val (subtree_compatible _ ⟨_, mem_of_append h⟩
      (by synth_isPosition) h)
    simp only [Set.mem_singleton_iff] at h'; rw [h']
    cases p <;> simp [ownTree, Player.toNat, Stream'.get]
  intro xr hx; induction' xr using List.reverseRecOn with xr b ih
  · simp
  · specialize ih (basicOpen_sub xr [b] hx); by_cases hp : IsPosition xr p
    · apply (subtree_compatible_iff _ ⟨_, ih⟩ hp).mpr
      simp_rw [Set.mem_singleton_iff, ownTree, subtree_incl_coe, ← h (xr.length / 2)]
      suffices b = x.get xr.length by cases p <;> (simp_all [IsPosition]; congr; omega)
      obtain ⟨_, _, rfl⟩ := hx; simp
    · rw [subtree_fair _ ⟨_, ih⟩ (by synth_isPosition)]; trivial
theorem Player.ownTree.disjoint {p} {a b : Stream' A} (h : a ≠ b) :
  body (ownTree p a).pre.subtree ∩ body (ownTree p b).pre.subtree = ∅ := by
  ext x; constructor
  · intro ⟨ha, hb⟩; apply h; ext n
    rw [← ownTree.mem_body.mp ha n, ← ownTree.mem_body.mp hb n]
  · simp
theorem QuasiStrategy.subtree_top_large {p} (h : 2 ≤ #A) (S : QuasiStrategy (⊤ : Tree A) p) :
  𝔠 ≤ #(body S.1.subtree) := by
  have h' : 𝔠 ≤ #(Stream' A) := by simpa [Stream'] using power_le_power_right h
  apply le_trans h' <| (le_def (Stream' A) _).mpr _
  have f := fun a : Stream' A ↦
    ((S.restrict (p.swap.ownTree a).pre).subtree_isPruned (
      (p.swap.ownTree a).quasi.subtree_isPruned <| Tree.top_isPruned (h := by
      rw [← mk_ne_zero_iff]; intro h'; simp [h'] at h))).body_ne_iff_ne.mpr (by
      simp)
  use fun a ↦ ⟨(f a).choose, by
    apply body_mono (PreStrategy.restrict_sub _ _ (PreStrategy.subtree_sub _)) (f a).choose_spec⟩
  intro a b; by_cases h : a = b
  · tauto
  · intro h'; exfalso
    refine (Player.ownTree.disjoint h).subset
      ⟨body_mono (PreStrategy.restrict_valid _ _ (PreStrategy.subtree_sub _)) (f a).choose_spec, ?_⟩
    have h := body_mono (PreStrategy.restrict_valid _ _ (PreStrategy.subtree_sub _)) (f b).choose_spec
    simp_rw [Subtype.mk.injEq] at h'; rwa [← h'] at h

@[simp] lemma card_player : #Player = 2 := by
  apply mk_eq_two_iff.mpr; use Player.zero, Player.one
  simp; ext p; cases p <;> tauto
theorem Game.exists_undetermined :
  ∃ G : Game (Fin 2), IsPruned G.tree ∧ [] ∈ G.tree ∧ ¬ G.IsDetermined := by
  let strat := (p : Player) × QuasiStrategy (⊤: Tree (Fin 2)) p
  have h : #strat ≤ 𝔠 := by
    have h : 𝔠 = #(Player × (List (Fin 2) → (Set (Fin 2)))) := calc 𝔠
      _ = 2 * 2 ^ (2 * ℵ₀) := by norm_num
      _ = 2 * (2 ^ 2) ^ ℵ₀ := by rw [power_mul]; rfl
      _ = #(Player × (List (Fin 2) → Set (Fin 2))) := by simp; norm_num
    rw [h, le_def] --via uncurry, use last?
    use fun ⟨p, f, _⟩ ↦ ⟨p, fun x ↦
      if h : IsPosition x p then Subtype.val '' f ⟨_, CompleteSublattice.mem_top⟩ h else ∅⟩
    intro ⟨p, ⟨s, hs⟩⟩ ⟨q, ⟨t, ht⟩⟩ h; simp_rw [Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
    congr!; ext x hp a
    have h : a.val ∈ Subtype.val '' s x hp ↔ a.val ∈ Subtype.val '' t x hp := by
      simpa only [hp, ↓reduceDIte, eq_iff_iff] using congr_fun (congr_fun h x) a.val
    simpa [Subtype.val_injective.mem_set_image] using h
  obtain ⟨losing : strat → Stream' (Fin 2), losing_inj, losing_lose⟩ :=
    Cardinal.choose_injection (fun (⟨_, s, _⟩ : strat) ↦ body s.subtree)
    (fun ⟨_, s⟩ ↦ le_trans h <| s.subtree_top_large (by simp))
  use ⟨⊤, {a | ∃ s, losing ⟨Player.one, s⟩ = a.val}⟩, fun _ ↦ ⟨0, by simp⟩, by simp
  intro ⟨p, ⟨s, hs⟩⟩; have alose := hs (losing_lose ⟨p, s.quasi⟩)
  cases p
  · have ⟨_, ⟨_, he⟩, hs'⟩ := alose; rw [← he] at hs'
    simpa using losing_inj hs'
  · have ⟨_, hs', he⟩ := alose; exact hs' ⟨_, he.symm⟩

end GaleStewartGame
--alternatively ultrafilters
