/-
  EPIC 002 — Faithful self-presentation (Def 2.2) + SEP-2.1
-/

import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4

namespace InfinityCompression.Core

structure FaithfulSelfPresentation (I : Type u1) (L : Type u2) (C : Type u3) (V : Type u4) extends
    SelfPresentedFamily I L C V where
  contact_injective : Function.Injective contact
  loc_contact_separates :
    ∀ i j : I, i ≠ j → ∃ l : L, loc l (contact i) ≠ loc l (contact j)

abbrev FaithfulSelfPresentation.toSPF {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    (F : FaithfulSelfPresentation I L C V) : SelfPresentedFamily I L C V :=
  F.toSelfPresentedFamily

/-- NV-2.2: `ℕ`-indexed family into `ℕ → Bool`, contact `id`, localization by application. -/
def nv22Faithful : FaithfulSelfPresentation ℕ (ℕ → Bool) ℕ Bool where
  obj := fun _ => fun _ => false
  contact := id
  loc := fun l c => l c
  contact_injective := Function.injective_id
  loc_contact_separates := fun i j hij => by
    classical
    refine ⟨fun n => decide (n = i), ?_⟩
    intro h_eq
    simp only [id_eq] at h_eq
    have hj : decide (j = i) = false := by simp [Ne.symm hij]
    have h_abs : decide True = false := Eq.trans h_eq hj
    simp at h_abs

theorem sep_faithful_excludes_constant_contact :
    ∀ (F : FaithfulSelfPresentation ℕ ℕ ℕ Bool),
      (∀ i : ℕ, F.contact i = 0) → False := by
  intro F hConst
  have heq : F.contact 0 = F.contact 1 := by rw [hConst, hConst]
  have : (0 : ℕ) = 1 := F.contact_injective heq
  cases this

example : Nonempty (FaithfulSelfPresentation ℕ (ℕ → Bool) ℕ Bool) :=
  ⟨nv22Faithful⟩

end InfinityCompression.Core
