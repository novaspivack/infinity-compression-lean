/-
  EPIC_019_GA1 — Split vs non-split examples, restriction to subgroups.

  1. Direct product as trivially-splitting extension (STRONG pattern).
  2. Non-splitting obstruction theorem (converse of splits_iff_trivial_cocycle).
  3. Restriction of extensions to subgroups via pullback.
  4. Global splitting implies local splitting.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.FiberArchitecture
import InfinityCompression.GeneralMethod.GroupExtension.SchurZassenhaus

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

/-! ### Trivially-splitting example: direct product extension -/

variable (N G : Type u) [Group N] [Group G]

def directProductExtension : GroupExtension N (N × G) G where
  inl := {
    toFun := fun n => (n, 1)
    map_one' := rfl
    map_mul' := fun a b => by simp [Prod.mul_def]
  }
  rightHom := {
    toFun := fun p => p.2
    map_one' := rfl
    map_mul' := fun a b => rfl
  }
  inl_injective := fun a b h => Prod.mk.inj h |>.1
  range_inl_eq_ker_rightHom := by
    ext ⟨n, g⟩
    constructor
    · rintro ⟨m, hm⟩
      show g = 1
      exact (Prod.mk.inj hm).2.symm
    · intro (hg : g = 1)
      exact ⟨n, Prod.ext rfl hg.symm⟩
  rightHom_surjective := fun g => ⟨(1, g), rfl⟩

def directProductSplitting : (directProductExtension N G).Splitting where
  toFun := fun g => (1, g)
  map_one' := rfl
  map_mul' := fun a b => by simp [Prod.mul_def]
  rightInverse_rightHom := fun g => rfl

theorem directProduct_splits : Nonempty (directProductExtension N G).Splitting :=
  ⟨directProductSplitting N G⟩

theorem directProduct_has_trivial_cocycle :
    ∃ σ : (directProductExtension N G).Section,
      ∀ g₁ g₂ : G, sectionCocycle (directProductExtension N G) σ g₁ g₂ = 1 :=
  (splits_iff_trivial_cocycle (directProductExtension N G)).mp
    ⟨directProductSplitting N G⟩

/-! ### Non-splitting obstruction theorem -/

variable {N G}
variable {E : Type u} [Group E] (S : GroupExtension N E G)

theorem not_splits_of_all_cocycles_nontrivial
    (h : ∀ σ : S.Section, ∃ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ ≠ 1) :
    ¬Nonempty S.Splitting := by
  intro ⟨s⟩
  obtain ⟨g₁, g₂, hne⟩ := h s.toSection
  apply hne
  apply S.inl_injective
  rw [sectionCocycle_spec, map_one]
  have : s.toSection.toFun g₁ = s g₁ := rfl
  have : s.toSection.toFun g₂ = s g₂ := rfl
  have : s.toSection.toFun (g₁ * g₂) = s (g₁ * g₂) := rfl
  simp only [*, s.map_mul', mul_inv_cancel]

theorem splits_section_independent :
    (∃ σ : S.Section, ∀ g₁ g₂ : G, sectionCocycle S σ g₁ g₂ = 1) ↔
    Nonempty S.Splitting :=
  (splits_iff_trivial_cocycle S).symm

/-! ### Restriction to subgroups via pullback -/

def pullbackSubgroup (H : Subgroup G) : Subgroup E where
  carrier := { e | S.rightHom e ∈ H }
  one_mem' := by simp [H.one_mem]
  mul_mem' := fun {a b} ha hb => by
    show S.rightHom (a * b) ∈ H
    rw [map_mul]
    exact H.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show S.rightHom a⁻¹ ∈ H
    rw [map_inv]
    exact H.inv_mem ha

def restrictExtension (H : Subgroup G) :
    GroupExtension N (pullbackSubgroup S H) H where
  inl := {
    toFun := fun n => ⟨S.inl n, by
      show S.rightHom (S.inl n) ∈ H
      rw [S.rightHom_inl]
      exact H.one_mem⟩
    map_one' := Subtype.ext (map_one S.inl)
    map_mul' := fun a b => Subtype.ext (map_mul S.inl a b)
  }
  rightHom := {
    toFun := fun e => ⟨S.rightHom e.val, e.property⟩
    map_one' := Subtype.ext (map_one S.rightHom)
    map_mul' := fun a b => Subtype.ext (map_mul S.rightHom a.val b.val)
  }
  inl_injective := fun a b h => S.inl_injective (congr_arg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext ⟨e, he⟩
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk,
               Subtype.ext_iff]
    constructor
    · rintro ⟨n, hn⟩
      show S.rightHom e = (1 : G)
      rw [← hn, S.rightHom_inl]
    · intro hker
      have : e ∈ S.rightHom.ker := by rwa [MonoidHom.mem_ker]
      rw [← S.range_inl_eq_ker_rightHom] at this
      obtain ⟨n, hn⟩ := this
      exact ⟨n, hn⟩
  rightHom_surjective := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he⟩ := S.rightHom_surjective g
    exact ⟨⟨e, by show S.rightHom e ∈ H; rw [he]; exact hg⟩, Subtype.ext he⟩

theorem splitting_restricts (H : Subgroup G) (s : S.Splitting) :
    Nonempty (restrictExtension S H).Splitting := by
  refine ⟨{
    toFun := fun h => ⟨s h.val, by
      show S.rightHom (s h.val) ∈ H
      rw [s.rightHom_splitting]
      exact h.property⟩
    map_one' := Subtype.ext (s.map_one')
    map_mul' := fun a b => Subtype.ext (s.map_mul' a.val b.val)
    rightInverse_rightHom := fun h => Subtype.ext (s.rightHom_splitting h.val)
  }⟩

theorem global_split_implies_local_split (H : Subgroup G) :
    Nonempty S.Splitting → Nonempty (restrictExtension S H).Splitting := by
  rintro ⟨s⟩
  exact splitting_restricts S H s

/-! ### Contrapositive: local non-splitting obstructs global splitting -/

theorem local_nonsplit_obstructs_global (H : Subgroup G)
    (h : ¬Nonempty (restrictExtension S H).Splitting) :
    ¬Nonempty S.Splitting :=
  fun hs => h (global_split_implies_local_split S H hs)

end InfinityCompression.GeneralMethod
