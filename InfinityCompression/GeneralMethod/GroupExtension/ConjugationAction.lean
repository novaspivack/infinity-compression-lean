/-
  EPIC_020_ML1 — Conjugation action of G on N via a section.

  Given a group extension `1 → N → E → G → 1` and a set-theoretic section `σ`,
  the group `G` acts on `N` by conjugation through the section:
    `φ_σ(g)(n) = inl⁻¹(σ(g) · inl(n) · σ(g)⁻¹)`

  Mathlib already provides `S.conjAct : E →* MulAut N`. We compose with a section
  to get `G → MulAut N` for a set-theoretic section, or `G →* MulAut N` for a splitting.

  Key results:
  - For commutative N, conjugation by kernel elements is trivial.
  - For commutative N, the action is independent of the section choice.
  - A splitting gives a group homomorphism `G →* MulAut N`.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import InfinityCompression.GeneralMethod.GroupExtension.FiberArchitecture

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

/-! ### Conjugation action via section -/

noncomputable def sectionConjAct (σ : S.Section) (g : G) : MulAut N :=
  S.conjAct (σ.toFun g)

theorem inl_sectionConjAct (σ : S.Section) (g : G) (n : N) :
    S.inl (sectionConjAct S σ g n) = σ.toFun g * S.inl n * (σ.toFun g)⁻¹ :=
  S.inl_conjAct_comm

/-! ### For commutative N, conjugation by kernel elements is trivial -/

section CommN

variable {N' E' G' : Type u} [CommGroup N'] [Group E'] [Group G']
variable (S' : GroupExtension N' E' G')

theorem conjAct_inl (n m : N') :
    S'.conjAct (S'.inl n) m = m := by
  apply S'.inl_injective
  rw [S'.inl_conjAct_comm]
  have h1 : S'.inl n * S'.inl m = S'.inl m * S'.inl n := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

/-! ### For commutative N, the action is independent of section choice -/

theorem sectionConjAct_independent (σ σ' : S'.Section) (g : G') (n : N') :
    sectionConjAct S' σ g n = sectionConjAct S' σ' g n := by
  apply S'.inl_injective
  rw [inl_sectionConjAct, inl_sectionConjAct]
  obtain ⟨m, hm⟩ := Section.mul_inv_mem_range_inl σ σ' g
  have hrel : σ.toFun g = S'.inl m * σ'.toFun g := by
    have : S'.inl m = σ.toFun g * (σ'.toFun g)⁻¹ := hm
    rw [this, inv_mul_cancel_right]
  rw [hrel]
  simp only [mul_inv_rev]
  have step : S'.inl m * σ'.toFun g * S'.inl n * ((σ'.toFun g)⁻¹ * (S'.inl m)⁻¹)
            = S'.inl m * (σ'.toFun g * S'.inl n * (σ'.toFun g)⁻¹) * (S'.inl m)⁻¹ := by group
  rw [step, ← inl_sectionConjAct S' σ' g n]
  set x := sectionConjAct S' σ' g n
  have key : S'.conjAct (S'.inl m) x = x := conjAct_inl S' m x
  have expand : S'.inl (S'.conjAct (S'.inl m) x) = S'.inl m * S'.inl x * (S'.inl m)⁻¹ :=
    S'.inl_conjAct_comm
  rw [key] at expand
  exact expand.symm

end CommN

/-! ### Splitting gives a group homomorphism G →* MulAut N -/

noncomputable def splittingConjAct (s : S.Splitting) : G →* MulAut N :=
  S.conjAct.comp s.toMonoidHom

theorem splittingConjAct_eq_sectionConjAct (s : S.Splitting) (g : G) :
    splittingConjAct S s g = sectionConjAct S s.toSection g :=
  rfl

end InfinityCompression.GeneralMethod
