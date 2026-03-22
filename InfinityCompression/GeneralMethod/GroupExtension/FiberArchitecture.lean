/-
  EPIC_019_GA1 — Positive-closure architecture applied to group extensions.

  Mathlib provides `GroupExtension N E G` (short exact sequence `1 → N → E → G → 1`),
  `Section` (set-theoretic right inverse of `rightHom`), and `Splitting` (homomorphic section).
  This module adds the **fiber / architecture** layer:

  - `ExtensionFiber S g` — the preimage fiber `π⁻¹(g)` as a subtype.
  - Fibers are nonempty (surjectivity of `rightHom`).
  - Each fiber is an `N`-torsor: the kernel acts freely and transitively.
  - The set-theoretic section always exists (`HasRightInverse`); the homomorphic section
    (splitting) is the *additional* structure whose existence/failure is the mathematical content.
  - Canonical fiber witnesses via `surjInvRightHom`.

  This is the first application of the positive-closure architecture to a problem where the
  distinction between set-theoretic sections and algebraic sections is load-bearing: every
  group extension has a set-theoretic section, but only split extensions have a homomorphic one.
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.GeneralMethod

open GroupExtension

variable {N E G : Type u} [Group N] [Group E] [Group G]
variable (S : GroupExtension N E G)

/-! ### Fibers of the extension projection -/

def ExtensionFiber (g : G) : Type u :=
  { e : E // S.rightHom e = g }

theorem extension_fiber_nonempty (g : G) : Nonempty (ExtensionFiber S g) := by
  obtain ⟨e, he⟩ := S.rightHom_surjective g
  exact ⟨⟨e, he⟩⟩

theorem rightHom_surjective_hasRightInverse :
    Function.HasRightInverse S.rightHom :=
  Function.Surjective.hasRightInverse S.rightHom_surjective

noncomputable def canonicalFiberWitness (g : G) : ExtensionFiber S g :=
  ⟨Function.surjInv S.rightHom_surjective g,
   Function.surjInv_eq S.rightHom_surjective g⟩

/-! ### Kernel action on fibers (N-torsor structure) -/

def kernelActOnFiber (g : G) (n : N) (x : ExtensionFiber S g) : ExtensionFiber S g :=
  ⟨S.inl n * x.val, by
    simp [S.rightHom_inl, x.property]⟩

theorem kernelAct_free (g : G) (n : N) (x : ExtensionFiber S g)
    (h : kernelActOnFiber S g n x = x) : n = 1 := by
  have heq : S.inl n * x.val = x.val := congr_arg Subtype.val h
  have hinl : S.inl n = 1 := by
    have : S.inl n * x.val * x.val⁻¹ = x.val * x.val⁻¹ := congr_arg (· * x.val⁻¹) heq
    simp [mul_assoc, mul_inv_cancel] at this
    exact this
  exact S.inl_injective (by rw [hinl, map_one])

theorem kernelAct_transitive (g : G) (x y : ExtensionFiber S g) :
    ∃ n : N, kernelActOnFiber S g n x = y := by
  have hmem : y.val * x.val⁻¹ ∈ S.rightHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, y.property, x.property, mul_inv_cancel]
  rw [← S.range_inl_eq_ker_rightHom] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, Subtype.ext (by simp [kernelActOnFiber, hn])⟩

/-! ### Set-theoretic section vs homomorphic splitting -/

theorem section_exists : Nonempty S.Section :=
  ⟨S.surjInvRightHom⟩

theorem section_is_rightInverse (σ : S.Section) :
    Function.RightInverse σ.toFun S.rightHom :=
  σ.rightInverse_rightHom

theorem splitting_iff_section_is_homomorphism :
    Nonempty S.Splitting ↔
    ∃ σ : S.Section, ∀ g₁ g₂ : G, σ.toFun (g₁ * g₂) = σ.toFun g₁ * σ.toFun g₂ := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.toSection, s.map_mul'⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨{
      toFun := σ.toFun
      map_one' := by
        have h1 := hσ 1 1
        simp only [mul_one] at h1
        have : σ.toFun 1 * (σ.toFun 1)⁻¹ = σ.toFun 1 * σ.toFun 1 * (σ.toFun 1)⁻¹ := by
          rw [← h1]
        simp [mul_assoc, mul_inv_cancel] at this
        exact this.symm
      map_mul' := hσ
      rightInverse_rightHom := σ.rightInverse_rightHom
    }⟩

/-! ### Architecture bundle summary

  For any group extension `S : GroupExtension N E G`:

  - **Bare layer** `B = G`, **enriched carrier** `E`, **forgetful map** `π = S.rightHom`.
  - **Fibers** `ExtensionFiber S g` are nonempty for all `g` (surjectivity).
  - **Set-theoretic section** always exists (`surjInvRightHom`): `HasRightInverse` holds.
  - **Homomorphic section** (splitting) exists iff the extension splits — this is the
    *additional algebraic constraint* beyond the set-theoretic baseline.
  - Each fiber is an `N`-torsor: the kernel acts freely and transitively.

  The gap between "set-theoretic section exists" and "homomorphic section exists" is
  precisely the mathematical content of extension theory. The positive-closure architecture
  makes this gap visible as a structural layer rather than a single yes/no predicate.
-/

end InfinityCompression.GeneralMethod
