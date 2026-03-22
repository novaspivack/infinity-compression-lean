/-
  EPIC 002 — Interaction structure (Def 2.4) + NV-2.4
-/

import Mathlib.Data.Finset.Basic

import InfinityCompression.Core.SelfPresentation

universe u1 u2 u3 u4

namespace InfinityCompression.Core

structure InteractionStructure (C : Type u3) where
  contactsInteract : Finset C → Prop

def SelfPresentedFamily.subfamilyInteracts {I : Type u1} {L : Type u2} {C : Type u3} {V : Type u4}
    [DecidableEq C] (F : SelfPresentedFamily I L C V) (IS : InteractionStructure C) (J : Finset I) :
    Prop :=
  IS.contactsInteract (J.image F.contact)

/-- NV-2.4: every finite set of contacts is declared interacting. -/
def nv24Interaction : InteractionStructure ℕ where
  contactsInteract := fun _ => True

example : Nonempty (InteractionStructure ℕ) :=
  ⟨nv24Interaction⟩

end InfinityCompression.Core
