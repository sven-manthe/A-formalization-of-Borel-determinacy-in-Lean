import BorelDet.Basic.misc_cat

open Classical CategoryTheory
universe u1 u2 v1 v2
variable {C : Type u2} {D : Type v2} [Category.{u1, u2} C] [Category.{v1, v2} D]

noncomputable section CZigzag
def CZag (c d : C) := (c ⟶ d) ⊕ (d ⟶ c)
def CZag.dom {c d : C} (_: CZag c d) := c
def CZag.codom {c d : C} (_: CZag c d) := d
inductive CZigzag : C → C → TypeMax.{u1, u2}
  | refl : (c : C) → CZigzag c c
  | cons : {c d e : C} → CZag c d → CZigzag d e → CZigzag c e
def CZigzag.trans {c d e : C} (x : CZigzag c d) (z : CZigzag d e) : CZigzag c e := match x with
  | refl d => z
  | cons x y => cons x (y.trans z)
def CZigzag.of_CZag {c d : C} (f : CZag c d) := cons f (refl _)
def CZigzag.append {c d e : C} (z : CZigzag c d) (f : CZag d e) := z.trans (of_CZag f)
def CZigzag.symm {c d : C} (z : CZigzag c d) : CZigzag d c := match z with
  | refl c => refl c
  | cons x y => y.symm.append x.swap
@[simp] theorem CZigzag.symm_refl {c : C} : (refl c).symm = refl c := by rfl
theorem nonempty_cZigzag_iff_zigzag (c d : C) : Nonempty (CZigzag c d) ↔ Zigzag c d := by
  constructor
  · intro ⟨h⟩; induction' h with _ _ _ _ de _ ih
    · exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single _) ih
      rcases de with f | f <;> [left; right] <;> exact ⟨f⟩
  · intro h; induction' h with _ _ _ de ih
    · exact ⟨CZigzag.refl c⟩
    · obtain ⟨cih⟩ := ih; constructor; apply cih.append; apply choice
      rcases de with f | f <;> constructor <;> [left; right] <;> exact choice f
theorem isConnected_iff_nonempty_cZigzag [Nonempty C]:
  IsConnected C ↔ ∀ c d : C, Nonempty (CZigzag c d) := by
  constructor <;> intro h
  · intro c d; apply (nonempty_cZigzag_iff_zigzag _ _).mpr; apply isPreconnected_zigzag
  · apply zigzag_isConnected; intro c d; apply (nonempty_cZigzag_iff_zigzag _ _).mp; apply h
def CZigzag.map {c d : C} (z : CZigzag c d) (F : C ⥤ D) :
  CZigzag (F.obj c) (F.obj d) := match z with
  | refl c => refl (F.obj c)
  | cons (Sum.inl f) y => cons (Sum.inl (F.map f)) (y.map F)
  | cons (Sum.inr f) y => cons (Sum.inr (F.map f)) (y.map F)
@[simp]theorem CZigzag.map_refl {c : C} (F : C ⥤ D) : (refl c).map F = refl (F.obj c) := rfl
@[simp]theorem CZigzag.map_trans {c d e : C} (F : C ⥤ D) (x : CZigzag c d) (y : CZigzag d e) :
  (x.trans y).map F = (x.map F).trans (y.map F) := by
  induction' x with _ _  _ _ f _ ih
  · rfl
  · cases f <;> simp [trans, map, ih]
@[simp]theorem CZigzag.map_symm {c d : C} (F : C ⥤ D) (z : CZigzag c d) :
  z.symm.map F = (z.map F).symm := by
  induction' z with _ _ _ _ f _ ih
  · simp
  · cases f <;> (simp [symm, trans, map, ih, append]; rfl)
def CZigzag.of_isos {c d : C} (z : CZigzag c d) := match z with
  | refl c => True
  | cons (Sum.inl f) z => IsIso f ∧ z.of_isos
  | cons (Sum.inr f) z => IsIso f ∧ z.of_isos
def CZigzag.of_isos.comp {c d : C} (z : CZigzag c d) (h : z.of_isos) : c ≅ d := match z, h with
  | refl c, _ => Iso.refl c
  | cons (Sum.inl f) z, h => have _: IsIso f := h.1; (asIso f).trans h.2.comp
  | cons (Sum.inr f) z, h => have _: IsIso f := h.1; (asIso f).symm.trans h.2.comp
abbrev ConstantSystem (F : C ⥤ D) := ∀ {c d} (f : c ⟶ d), IsIso (F.map f)
theorem CZigzag.ConstantSystem.map_of_isos {c d : C} {F : C ⥤ D}
  (h : ConstantSystem F) (z : CZigzag c d) : (z.map F).of_isos := match z with
  | refl _ => trivial
  | cons (Sum.inl _) _ => by constructor; apply h; apply map_of_isos h
  | cons (Sum.inr _) _ => by constructor; apply h; apply map_of_isos h
def CZigzag.constantSystem_comp {c d : C} {F : C ⥤ D}
  (h : ConstantSystem F) (z : CZigzag c d) := (ConstantSystem.map_of_isos h z).comp
@[simp] theorem CZigzag.comp_refl {F : C ⥤ D} (h : ConstantSystem F) {c : C} :
  (refl c).constantSystem_comp h = Iso.refl _ := by rfl
@[simp] theorem CZigzag.comp_cons_left {F : C ⥤ D} {c d e : C} {f : e ⟶ c}
  (h : ConstantSystem F) (z : CZigzag c d) :
  have _: IsIso (F.map f) := by apply h
  (cons (Sum.inl f) z).constantSystem_comp h
  = (asIso (F.map f)).trans (z.constantSystem_comp h) := rfl
@[simp] theorem CZigzag.comp_cons_right {F : C ⥤ D} {c d e : C} {f : c ⟶ e}
  (h : ConstantSystem F) (z : CZigzag c d) :
  have _: IsIso (F.map f) := by apply h
  (cons (Sum.inr f) z).constantSystem_comp h
  = (asIso (F.map f)).symm.trans (z.constantSystem_comp h) := rfl
@[simp] theorem CZigzag.comp_trans {F : C ⥤ D} {c d e : C} (h : ConstantSystem F)
  (x : CZigzag c d) (y : CZigzag d e) : (x.trans y).constantSystem_comp h
    = (x.constantSystem_comp h).trans (y.constantSystem_comp h) := by
  induction' x with _ _ _ _ f a ih
  · simp; rfl
  · cases f <;> (simp [trans] at *; rw [ih])
@[simp] theorem CZigzag.comp_symm {F : C ⥤ D} {c d : C} (h : ConstantSystem F) (z : CZigzag c d) :
  z.symm.constantSystem_comp h = (z.constantSystem_comp h).symm := by
  induction' z with _ a b c f z ih; simp
  cases f <;>
    (simp [symm, map, append] at *; simp [constantSystem_comp, of_isos.comp] at *; rw [ih])
abbrev MorphismFinset C [Category C] := Finset (Σ c d : C, c ⟶ d)
def MorphismFinset.objSet (A : MorphismFinset C) : Finset C :=
  Finset.image (fun ⟨c, _, _⟩ ↦ c) A ∪ Finset.image (fun ⟨_, c, _⟩ ↦ c) A
@[simp] theorem MorphismFinset.mono_objSet {A B : MorphismFinset C} (h : A ⊆ B) :
  A.objSet ⊆ B.objSet := by
    simp [objSet]; apply Finset.union_subset_union <;> exact Finset.image_subset_image h
@[simp] theorem MorphismFinset.objSet_sing {c d : C} (f : c ⟶ d) :
  ({⟨c, d, f⟩} : MorphismFinset C).objSet = {c, d} := by simp [objSet]; aesop
@[simp] theorem MorphismFinset.insert_objSet (A : MorphismFinset C) {c d : C} (f : c ⟶ d) :
  (A ∪ {⟨c, d, f⟩}).objSet = A.objSet ∪ {c, d} := by
  simp only [objSet, Finset.image_union, Finset.image_singleton, Finset.union_assoc,
    Finset.union_insert]; aesop
def MorphismFinset.retyped (A : MorphismFinset C) {B : Finset C} (_: A.objSet ⊆ B) :
  Finset (Σ' (c d : C) (_: c ∈ B) (_: d ∈ B), c ⟶ d) :=
  A.preimage (fun ⟨c, d, _, _, f⟩ ↦ ⟨c, d, f⟩) (by aesop_cat)
def MorphismFinset.retyped' (A : MorphismFinset C) := A.retyped Finset.Subset.rfl
def CZigzag.morphismSet {c d : C} (z : CZigzag c d) : MorphismFinset C := match z with
  | refl c => {⟨c, _, 𝟙 _⟩}
  | cons (Sum.inl f) z => {⟨_, _, f⟩} ∪ z.morphismSet
  | cons (Sum.inr f) z => {⟨_, _, f⟩} ∪ z.morphismSet
@[simp] theorem CZigzag.objSet_cons {c d e : C} (f : CZag c d) (z : CZigzag d e) :
  (cons f z).morphismSet.objSet = z.morphismSet.objSet ∪ {c, d} := by
  cases f <;> (simp [morphismSet, Finset.image_union]; rw [Finset.union_comm]; simp); aesop
theorem CZigzag.objSet_left {c d : C} (z : CZigzag c d) : c ∈ z.morphismSet.objSet := by
  cases z <;> simp [morphismSet]
theorem CZigzag.objSet_right {c d : C} (z : CZigzag c d) : d ∈ z.morphismSet.objSet := by
  induction' z <;> simp [morphismSet, *]
variable [IsFiltered C] {F : C ⥤ D} (hF : ConstantSystem F)
theorem CZigzag.constantSystem_comp_cone {c d : C} (z : CZigzag c d) A (hA : z.morphismSet ⊆ A) :
  F.map (IsFiltered.toSup _ A.retyped' ((MorphismFinset.mono_objSet hA) z.objSet_left))
  = (z.constantSystem_comp hF).hom
  ≫ F.map (IsFiltered.toSup _ A.retyped' ((MorphismFinset.mono_objSet hA) z.objSet_right)) := by
  induction' z with c d a b f z ih; simp
  specialize ih (by
    cases f <;>
      {simp [morphismSet] at hA; exact Finset.Subset.trans (by apply Finset.subset_union_right) hA})
  cases f <;> simp [← ih]
  symm; all_goals {
    rw [← F.map_comp]; congr; apply IsFiltered.toSup_commutes;
    simp [MorphismFinset.retyped, MorphismFinset.retyped']; apply hA; simp [morphismSet] }
theorem CZigzag.constantSystem_comp_cone_const {c : C} (z : CZigzag c c) :
  z.constantSystem_comp hF = Iso.refl _ := by
  have h' := z.constantSystem_comp_cone hF z.morphismSet (by simp)
  ext; exact (cancel_mono_id _).mp h'.symm
theorem CZigzag.constantSystem_comp_uniq {c d : C} (z z' : CZigzag c d) :
  z.constantSystem_comp hF = z'.constantSystem_comp hF := by
  ext; rw [← comp_inv_eq_id]
  simpa using congr_arg Iso.hom (constantSystem_comp_cone_const hF (z.trans  z'.symm))

def hom_constantSystem (c d : C) : F.obj c ⟶ F.obj d :=
  ((choice (isConnected_iff_nonempty_cZigzag.mp inferInstance c d)).constantSystem_comp hF).hom
instance (c d : C) : IsIso (hom_constantSystem hF c d) :=
  by simp [hom_constantSystem]; infer_instance
theorem hom_constantSystem.eq_constantSystem_comp {c d : C} (z : CZigzag c d) :
  hom_constantSystem hF c d = (z.constantSystem_comp hF).hom := by
  simp [hom_constantSystem]; congr 1; apply CZigzag.constantSystem_comp_uniq
theorem hom_constantSystem.eq_F_map {c d : C} (f : c ⟶ d) :
  F.map f = hom_constantSystem hF c d := by
  rw [eq_constantSystem_comp hF (CZigzag.of_CZag (Sum.inl f))]
  simp [CZigzag.constantSystem_comp, CZigzag.of_isos.comp]
@[simp] theorem hom_constantSystem.refl {c : C} : hom_constantSystem hF c c = 𝟙 _ := by
  rw [← eq_F_map hF (𝟙 c)]; apply CategoryTheory.Functor.map_id
@[simp] theorem hom_constantSystem.symm {c d : C} :
  inv (hom_constantSystem hF d c) = hom_constantSystem hF c d := by
  obtain ⟨z⟩ := isConnected_iff_nonempty_cZigzag.mp inferInstance c d
  nth_rw 1 [eq_constantSystem_comp hF z]; simp [eq_constantSystem_comp hF z.symm]
@[simp] theorem hom_constantSystem.trans {c d e : C} :
  hom_constantSystem hF c d ≫ hom_constantSystem hF d e = hom_constantSystem hF c e := by
  obtain ⟨z1⟩ := isConnected_iff_nonempty_cZigzag.mp inferInstance c d
  obtain ⟨z2⟩ := isConnected_iff_nonempty_cZigzag.mp inferInstance d e
  rw [eq_constantSystem_comp hF z1, eq_constantSystem_comp hF z2,
    eq_constantSystem_comp hF (z1.trans z2)]; simp
@[simp] theorem hom_constantSystem.natTrans {c d : C} {x : D} (α: F ⟶ (Functor.const C).obj x) :
  hom_constantSystem hF c d ≫ α.app d = α.app c := by
  obtain ⟨z⟩ := isConnected_iff_nonempty_cZigzag.mp inferInstance c d
  rw [eq_constantSystem_comp hF z]
  induction' z with _ _ _ _ f z' ih; simp
  cases f <;> simp [ih]

def trivial_colimit_cocone (x : C) : Limits.Cocone F where
  pt := F.obj x
  ι := {
    app := fun c ↦ hom_constantSystem hF c x
    naturality := by
      intros _ _ f; rw [hom_constantSystem.eq_F_map hF f]; simp
  }
def trivial_isColimit (x : C) : Limits.IsColimit (trivial_colimit_cocone hF x) where
  desc := fun s ↦ s.ι.app x
  fac := by unfold trivial_colimit_cocone; aesop_cat
  uniq := by unfold trivial_colimit_cocone; intros _ _ c; specialize c x; aesop_cat
instance {G : C ⥤ D} {s t : Limits.Cocone G} (f : s ⟶ t) [IsIso f] : IsIso f.hom := by
  use (inv f).hom; constructor
  show (f ≫ inv f).hom = (𝟙 s : s ⟶ s).hom; simp
  show (inv f ≫ f).hom = (𝟙 t : t ⟶ t).hom; simp
instance const_incl_isIso {s : Limits.Cocone F} (hl : Limits.IsColimit s) c :
  IsIso (s.ι.app c) := by
  obtain f : trivial_colimit_cocone hF c ≅ s :=
    Limits.IsColimit.uniqueUpToIso (trivial_isColimit _ _) hl
  have heq : (trivial_colimit_cocone hF c).ι.app c ≫ f.hom.hom = s.ι.app c := by apply f.hom.w
  unfold trivial_colimit_cocone at heq
  rw [← heq]; simp; infer_instance
end CZigzag
instance const_proj_isIso [IsCofiltered C] {F : C ⥤ D} (hF : ConstantSystem F) {s : Limits.Cone F}
  (hl : Limits.IsLimit s) c : IsIso (s.π.app c) := by
  have hop : ConstantSystem F.op := by
    intros _ _ f; exact (isIso_unop_iff (F.op.map f)).mp (hF f.unop)
  have resop : IsIso (s.op.ι.app (Opposite.op c)) := const_incl_isIso hop (Limits.IsLimit.op hl) _
  simp at resop; exact isIso_of_op (s.π.app c)
