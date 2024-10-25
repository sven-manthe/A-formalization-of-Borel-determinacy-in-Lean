import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.ContinuousMap.Basic

--import Mathlib.Topology.Category.TopCat.Basic --relevant file

open CategoryTheory

variable (C : Type) [Category C] [ConcreteCategory C]

attribute [local instance] ConcreteCategory.hasCoeToSort --copied from Mathlib.CategoryTheory.ConcreteCategory.Basic

-- Porting note : cannot find a coercion to function otherwise
attribute [instance] ConcreteCategory.instFunLike
instance (X Y : C) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f--copied from Mathlib.Topology.Category.TopCat.Basic, where instead of C they use Top
