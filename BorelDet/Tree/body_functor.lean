import BorelDet.Tree.tree_body
import BorelDet.Tree.len_tree_hom

namespace GaleStewartGame.Tree
open CategoryTheory
open InfList

variable {A A' : Type*} {n : ℕ}

noncomputable section
variable {S : Tree A} {T : Tree A'}
def bodyDom (f : OrderHom S T) : Set (ℕ → A) := { a | a ∈ body S ∧
  Set.Unbounded Nat.le ((fun (x : S) ↦ (f x).val.length) '' { x | a ∈ basicOpen x }) }
theorem bodyMap_uniq (f : OrderHom S T) {a : ℕ → A} {x y : List A}
  {ha : a ∈ body S} (hx : a ∈ basicOpen x) (hy : a ∈ basicOpen y)
  (hlx : n < (f ⟨x, ha x hx⟩).val.length) (hly : n < (f ⟨y, ha y hy⟩).val.length) :
  (f ⟨x, ha x hx⟩).val[n] = (f ⟨y, ha y hy⟩).val[n] := by
  wlog h : x.length ≤ y.length
  · exact (this f hy hx hly hlx <| Nat.le_of_lt (by simpa using h)).symm
  · have hpr : (f ⟨x, ha x hx⟩).val <+: f ⟨y, ha y hy⟩ := by
      apply f.monotone'; show x <+: y
      rw [basicOpen_iff_restrict] at *
      rw [hx, hy]; simp [h]
    simp_rw (config := {singlePass := true}) [List.prefix_iff_eq_take.mp hpr]
    apply List.getElem_take
theorem bodyMap_exists (f : OrderHom S T) (a : bodyDom f) (n : ℕ) :
  ∃ (x : S), (a : ℕ → A) ∈ basicOpen x ∧ n < (f x).val.length := by
  obtain ⟨b, ⟨⟨x, hx, rfl⟩, h''⟩⟩ := a.prop.2 n; use x, hx; simpa using h''
def bodyMap_choose_spec (f : OrderHom S T) (a : bodyDom f) (n : ℕ) : T :=
  let t := bodyMap_exists f a n; f ⟨t.choose, a.prop.1 t.choose t.choose_spec.1⟩
def bodyMap_val (f : OrderHom S T) (a : bodyDom f) (n : ℕ) : A' :=
  let t := bodyMap_exists f a n; (f t.choose).val[n]
theorem bodyMap_pspec (f : OrderHom S T) (a : bodyDom f) {x}
  (hx : (a : ℕ → A) ∈ basicOpen x) (hlx : n < (f ⟨x, a.prop.1 x hx⟩).val.length) :
  bodyMap_val f a n = (f ⟨x, a.prop.1 x hx⟩).val[n] := by
  simp [bodyMap_val]; rw [bodyMap_uniq _ _ (bodyMap_exists f a n).choose_spec.1]; rfl

def bodyMap (f : OrderHom S T) (a : bodyDom f) : body T :=
  ⟨bodyMap_val f a, by
    intro y hy; apply mem_of_prefix (y := bodyMap_choose_spec f a y.length) _ (SetLike.coe_mem _)
    rw [basicOpen_iff_restrict] at hy; nth_rw 1 [hy]; apply List.prefix_iff_eq_take.mpr
    have ⟨hx, hl⟩ := (bodyMap_exists f a y.length).choose_spec
    apply List.ext_getElem
    · simp [bodyMap_choose_spec, hl.le]
    · intro n hn _; simp at hn; simp [hn, bodyMap_choose_spec]
      rw [(bodyMap_pspec f a hx (lt_trans hn hl))]; rfl⟩
theorem bodyMap_spec (f : OrderHom S T) (a : bodyDom f) {x}
  (hx : (a : ℕ → A) ∈ basicOpen x) (hlx : n < (f ⟨x, a.prop.1 x hx⟩).val.length) :
  (bodyMap f a).val n = (f ⟨x, a.prop.1 x hx⟩).val[n] := bodyMap_pspec f a hx hlx
theorem bodyMap_continuous (f : OrderHom S T)
  [TopologicalSpace A] [TopologicalSpace A'] [DiscreteTopology A] [DiscreteTopology A']:
  Continuous (bodyMap f) := by
  apply continuous_iff_continuousAt.mpr; intro a
  have h := hasBasis_basicOpen (bodyMap f a : ℕ → A')
  have hc := h.comap (fun (x : body T) ↦ x.val)
  rw [← nhds_subtype] at hc; apply hc.tendsto_right_iff.mpr; intro y hy
  have ⟨x, hxa, hxl⟩ := bodyMap_exists f a y.length
  apply Filter.eventually_of_mem (U :=_root_.Subtype.val⁻¹' (basicOpen x))
  · rw [mem_nhds_iff]; use _root_.Subtype.val⁻¹' (basicOpen x)
    constructor; exact subset_rfl; constructor
    apply continuous_subtype_val.isOpen_preimage; apply basicOpen_isOpen
    exact hxa
  · intro b hb
    simp; rw [basicOpen_index]; intro n hn; rw [← ((basicOpen_index y).mp hy) n hn]
    rw [bodyMap_spec f b hb (lt_trans hn hxl)]
    rw [bodyMap_spec f a hxa (lt_trans hn hxl)]

instance (S : Trees) : TopologicalSpace S.1 := ⊥
instance (S : Trees) : DiscreteTopology S.1 where eq_bot := rfl
variable {S T : Trees}
--also make functor to TopCat?
@[simp] theorem bodyDom_univ (f : S ⟶ T) : bodyDom f.toOrderHom = body S.2 := by
  simp only [bodyDom, Set.sep_eq_self_iff_mem_true]; intro x hx n; use n + 1; simp
  use x.take (n + 1); dsimp [body] at hx; simp [hx]
@[simps obj] def bodyPre : Prefunctor Trees (Type*) where
  obj S := body S.2
  map f a := bodyMap f.toOrderHom ⟨a, by simp⟩
@[ext] theorem bodyPre_obj_ext {x y : bodyPre.obj S} (h : x.val = y.val) : x = y := by
  dsimp; ext1; exact h
instance : CoeFun (bodyPre.obj S) (fun _ ↦ ℕ → S.1) where coe x := x.val
theorem LenHom.bodyMap_spec (f : S ⟶ T) (a : body S.2)
  x (hx : (a : ℕ → S.1) ∈ basicOpen x) n (hlx : n < x.length) :
  (bodyPre.map f a) n = (f ⟨x, a.prop x hx⟩).val[n]'(by simpa) := by
  apply Tree.bodyMap_spec f.toOrderHom _ hx
theorem LenHom.bodyMap_spec_res_lt (f : S ⟶ T) (a : body S.2) {m n} (h : m < n) :
  (bodyPre.map f a) m = (f (body.take n a)).val[m]'(by simpa)  :=
  bodyMap_spec f a (a.val.take n) (by simp) m (by simp [h])
theorem LenHom.bodyMap_spec_res (f : S ⟶ T) (a : body S.2) n :
  (bodyPre.map f a) n = (f (body.take (n + 1) a)).val[n]  :=
  bodyMap_spec_res_lt f a (Nat.lt_succ_self n)
@[simps! obj] def bodyFunctor : Trees ⥤ Type* where
  toPrefunctor := bodyPre
  map_id _ := by
    ext; simp [LenHom.bodyMap_spec_res]
  map_comp f g := by
    ext x n; simp [LenHom.bodyMap_spec_res]
    congr!; ext1; apply List.ext_getElem (by simp); intro m hm
    simp [hm, take_eval, LenHom.bodyMap_spec_res_lt _ _ hm]
@[simps] instance : CoeFun (Tree.bodyFunctor.obj S) (fun _ ↦ ℕ → S.1) where coe x := x.val
instance bodySpace : TopologicalSpace (Tree.bodyFunctor.obj S) := by
  dsimp; infer_instance
theorem bodyMap_spec' (f : S ⟶ T) (a : body S.2)
  x (hx : (a : ℕ → S.1) ∈ basicOpen x) n (hlx : n < x.length) :
  (bodyFunctor.map f a) n = (f ⟨x, a.prop x hx⟩).val[n]'(by simpa) :=
  LenHom.bodyMap_spec f a x hx n hlx
theorem bodyMap_spec_res_lt' (f : S ⟶ T) (a : body S.2) {m n} (h : m < n) :
  (bodyFunctor.map f a) m = (f (body.take n a)).val[m]'(by simpa)  :=
  LenHom.bodyMap_spec_res_lt f a h
theorem bodyMap_spec_res' (f : S ⟶ T) (a : body S.2) n :
  (bodyFunctor.map f a) n = (f ⟨a.val.take (n + 1), a.prop _ (by simp)⟩).val[n]  :=
  LenHom.bodyMap_spec_res f a n
@[simp] theorem bodyMap_restrict {S T : Trees} (f : S ⟶ T) a n :
  (bodyFunctor.map f a).val.take n = (f (body.take n a)).val := by
  apply List.ext_getElem <;> simp
  intro m hm; rw [← bodyMap_spec_res_lt' f a hm]
lemma LenHom.bodyMap_continuous {S T : Trees} (f : S ⟶ T) :
  Continuous (bodyFunctor.map f) := by
  dsimp [bodyFunctor, bodyPre, bodySpace]
  convert Tree.bodyMap_continuous f.toOrderHom <;> simp only [bodyDom_univ]

end
end GaleStewartGame.Tree
