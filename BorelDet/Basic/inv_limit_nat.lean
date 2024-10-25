import BorelDet.Basic.constant_colimit

open Classical CategoryTheory

universe u u1 u2
section Preorder
variable {X Y : Type u} [Preorder X] [Preorder Y] {x y z : X}
@[simp] lemma homOfLE_refl' (h : x ≤ x) : homOfLE h = 𝟙 x := rfl
@[simp] lemma homOfLE_comp' (h : x ≤ y) (k : y ≤ z) (u : x ≤ z) :
  homOfLE h ≫ homOfLE k = homOfLE u := rfl
lemma eq_homOfLE (f : x ⟶ y) : f = homOfLE (leOfHom f) := by apply Subsingleton.elim
@[simp] lemma map_eq_homOfLE (F : X ⥤ Y) (f : x ⟶ y) :
  F.map f = homOfLE (leOfHom (F.map f)) := by apply Subsingleton.elim
def structuredArrow_preorder (y : Y) {f : X → Y} (h : Monotone f) :
  StructuredArrow y h.functor ≌ {x | y ≤ f x} where
  functor := {
    obj := fun A ↦ ⟨A.2, A.hom.le⟩
    map := fun AB ↦ AB.2.le.hom
  }
  inverse := {
    obj := fun x ↦ StructuredArrow.mk x.prop.hom
    map := by intro x y xy; apply StructuredArrow.homMk; swap; apply homOfLE; exact leOfHom xy; apply Subsingleton.elim
  }
  unitIso := eqToIso (by rfl)
  counitIso := eqToIso (by rfl)
--something similar holds for any Category, but then we need the codomain filtered
theorem final_of_structuredArrow_nonempty [IsDirected X LE.le] (F : X ⥤ Y)
  (h : ∀ y, Nonempty {x | y ≤ F.obj x}) : F.Final := by
  constructor; intro y
  suffices IsDirected {x | y ≤ F.obj x} LE.le by
    apply isConnected_of_equivalent (structuredArrow_preorder y F.monotone).symm
  constructor; intros a b; obtain ⟨c, h1, h2⟩ := directed_of LE.le a.val b.val
  use ⟨c, le_trans a.prop (F.monotone h1)⟩; exact ⟨h1, h2⟩
end Preorder

variable {C : Type u2} [Category.{u1, u2} C]
lemma heq_eqToHom {a b c d : C} (ab : a = b) (bc : b = c) (cd : c = d) : HEq (eqToHom ab) (eqToHom cd) := by
  subst ab bc cd; rfl
theorem left_eqToHom_iff_heq {W X Y : C} (f : W ⟶ X) (g : Y ⟶ X) (h : W = Y) :
  f = eqToHom h ≫ g ↔ HEq f g := by cases h; simp
lemma congr_comp {a b b' c d : C} (f : c ⟶ d) {g : b ⟶ c} {g' : b' ⟶ c} {h : a ⟶ b} {h' : a ⟶ b'}
  (H : h ≫ g = h' ≫ g') : h ≫ g ≫ f = h' ≫ g' ≫ f := by
  replace H := congr_fun (congr_arg CategoryStruct.comp H) f; simp at H; exact H
def recComp m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) : F (m + n) ⟶ F m := by
  induction' n with n ih; exact 𝟙 (F m); exact f (m + n) ≫ ih
theorem recComp_induction (p : ∀ ⦃c d⦄, (c ⟶ d) → Prop) (pid : ∀ c, p (𝟙 c))
  (pcomp : ∀ {c d e}(f : c ⟶ d) (g : d ⟶ e), p f → p g → p (f ≫ g)) m n {F : ℕ → C}
  (f : ∀ n, F (n + 1) ⟶ F n) (h : ∀ n, p (f (m + n))) : p (recComp m n f) := by
  induction' n with n ih; exact pid _; exact pcomp _ _ (h _) ih
instance recComp_iso m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : ∀ n, IsIso (f (m + n))) :
  IsIso (recComp m n f) := by
  apply recComp_induction <;> (intros; infer_instance)
def recCompOfLE {m n} (h : m ≤ n) {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) : F n ⟶ F m :=
  eqToHom (by simp [h]) ≫ recComp m (n - m) f
@[simp]theorem recComp.eq_zero m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : n = 0) :
  recComp m n f = eqToHom (by subst h; rfl) := by subst h; rfl
@[simp]theorem recCompOfLE.refl n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) :
  recCompOfLE (le_refl n) f = 𝟙 (F n) := by simp [recCompOfLE]
@[simp]theorem recComp.sum m n p {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) :
  recComp (m + n) p f ≫ recComp m n f
  = eqToHom (by simp [Nat.add_assoc]) ≫ recComp  m (n + p) f := by
  induction' p with p ih; rfl
  simp [recComp, Nat.recAux] at *; rw [ih]
  apply congr_comp; symm; apply (IsIso.eq_inv_comp _).mp; simp
  apply (conj_eqToHom_iff_heq _ _ _ _).mpr; all_goals (congr 1; simp [Nat.add_assoc])
@[simp]theorem recComp.eq_sum m n p q {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : p = m + n) :
  recComp p q f ≫ eqToHom (by rw [h]) ≫ recComp m n f
  = eqToHom (by rw [h]; congr 1; simp [Nat.add_assoc]) ≫ (recComp m (n + q) f) := by subst h; simp
@[simp]theorem recCompOfLE.trans m n p {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h1: m ≤ n) (h2: n ≤ p) :
  recCompOfLE h2 f ≫ recCompOfLE h1 f = recCompOfLE (le_trans h1 h2) f := by
  simp [recCompOfLE]; rw [recComp.eq_sum]; simp
  apply (IsIso.eq_inv_comp _).mp; simp
  apply (left_eqToHom_iff_heq _ _ _).mpr; congr
  all_goals simp [h1, h2]
@[simp]theorem recComp.eq_one m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : n = 1) :
  eqToHom (by rw [h]) ≫ recComp m n f = f m := by subst h; simp [recComp]
@[simp]theorem recComp.functor m n (F : ℕᵒᵖ ⥤ C) :
  recComp m n (F := F.obj ∘ Opposite.op) (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  = F.map (homOfLE (Nat.le_add_right m n)).op := by
  induction' n with n ih; simp
  simp [recComp, Nat.recAux] at *; rw [ih, ← F.map_comp]; congr 1
noncomputable def nat_free_cat : (ℕᵒᵖ ⥤ C) ≃ ((O : ℕ → C) × (∀ n, O (n + 1) ⟶ O n)) where
  toFun F := ⟨F.obj ∘ Opposite.op, fun n ↦ F.map (homOfLE (Nat.le_succ n)).op⟩
  invFun := fun ⟨O, F⟩ ↦ {
    obj := O ∘ Opposite.unop
    map := @fun m n ↦ fun h ↦ eqToHom (by simp [leOfHom h.unop]) ≫ (recComp n.unop (m.unop-n.unop) F)
    map_comp := by
      intros m n k h1 h2; simp [leOfHom h1.unop, leOfHom h2.unop]
      congr 1; swap; apply heq_eqToHom; pick_goal 3; congr
      all_goals simp [Nat.add_sub_sub_of_le, leOfHom h1.unop, leOfHom h2.unop, leOfHom (h1 ≫ h2).unop]
  }
  left_inv F := by
    apply CategoryTheory.Functor.ext; swap; intro _; rfl
    intros m n h; simp; symm; apply (left_eqToHom_iff_heq _ _ _).mpr
    congr 1; swap; apply Subsingleton.helim; congr; all_goals simp [leOfHom h.unop]
  right_inv _ := by ext <;> simp
@[simp] lemma nat_free_cat_apply_symm_apply (x : (O : ℕ → C) × (∀ n, O (n + 1) ⟶ O n)) :
  (nat_free_cat (nat_free_cat.symm x)).2 = x.2 := by
  congr; rw [Equiv.apply_symm_apply]

variable {C : Type u2} [Category.{u1, u2} C]
theorem constantSystem_nat (F : ℕᵒᵖ ⥤ C) (hF : ∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
  ConstantSystem F := by
  rintro ⟨c⟩ ⟨d⟩ ⟨f⟩; obtain ⟨k, rfl⟩ := le_iff_exists_add.mp (leOfHom f)
  erw [← recComp.functor]; have hf : ∃ h, f = homOfLE h := ⟨_, eq_homOfLE f⟩
  obtain ⟨hf, rfl⟩ := hf; apply recComp_iso; intro _; apply hF
@[simps! obj] def additionNatFunctor (k : ℕ) : ℕ ⥤ ℕ :=
  Monotone.functor (f := (· + k)) (by aesop_cat)
instance (k : ℕ) : Functor.Final (additionNatFunctor k) := by
  apply final_of_structuredArrow_nonempty; intro n; use n; simp
theorem nat_add_initial {F : ℕᵒᵖ ⥤ C} {s : Limits.Cone F} (hs : Limits.IsLimit s)
  n (hn : ∀ k ≥ n, IsIso (F.map (homOfLE (Nat.le_succ k)).op)) k (hk : n ≤ k) :
  IsIso (s.π.app (Opposite.op k)) := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hk
  suffices IsIso (s.π.app ((additionNatFunctor n).op.obj (Opposite.op k))) by
    convert this <;> simp [add_comm]
  let s' := s.whisker (additionNatFunctor n).op
  let hs' := (Functor.Initial.isLimitWhiskerEquiv (additionNatFunctor n).op s).symm hs
  have hcons : ConstantSystem ((additionNatFunctor n).op ⋙ F) := by
    apply constantSystem_nat; intro k; specialize hn (k + n) (by simp)
    simp [additionNatFunctor]
    convert hn using 3 <;> simp [Nat.succ_add]
    apply Subsingleton.helim; congr
  exact const_proj_isIso hcons (s := s') hs' (Opposite.op k)
