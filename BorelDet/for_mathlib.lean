import Mathlib.Tactic

--TODO trans ∈ ⊆, similar filters (what's there?)
--TODO namespace not_imp_self
attribute [refl] List.prefix_refl
@[refl] lemma iff_self' {a : Prop} : a ↔ a := Iff.rfl
--@[refl] lemma imp_self' {a : Prop} : a → a := id
