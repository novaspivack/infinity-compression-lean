/-
  EPIC_022_OP1 Phase C2 — Elliptic curve descent: 2-torsion fiber architecture.

  For an abelian group A, the doubling map has fibers that are cosets of the
  2-torsion subgroup. We formalize this torsor structure and connect it to
  elliptic curve descent via Mathlib's twoTorsionPolynomial.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.GeneralMethod.Descent

open WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem twoTorsionPoly_discr_eq :
    W.twoTorsionPolynomial.discr = 16 * W.Δ :=
  W.twoTorsionPolynomial_discr

/-! ### Abstract doubling map and fibers -/

variable {A : Type u} [AddCommGroup A]

def doublingMap : A →+ A where
  toFun := fun a => a + a
  map_zero' := add_zero 0
  map_add' := fun a b => by abel

def DoublingFiber (p : A) : Type u :=
  { q : A // q + q = p }

def TwoTorsionSet : Set A :=
  { a : A | a + a = 0 }

/-! ### 2-torsion acts on fibers -/

def twoTorsionActOnFiber (p : A) (t : TwoTorsionSet (A := A)) (q : DoublingFiber p) :
    DoublingFiber p :=
  ⟨t.val + q.val, by
    have ht : t.val + t.val = 0 := t.property
    have hq : q.val + q.val = p := q.property
    calc t.val + q.val + (t.val + q.val)
        = (t.val + t.val) + (q.val + q.val) := by abel
      _ = 0 + p := by rw [ht, hq]
      _ = p := zero_add p⟩

theorem twoTorsionAct_free (p : A) (t : TwoTorsionSet (A := A))
    (q : DoublingFiber p)
    (h : twoTorsionActOnFiber p t q = q) : t.val = 0 := by
  have heq : t.val + q.val = q.val := congr_arg Subtype.val h
  have : t.val = t.val + q.val + (-q.val) := by abel
  rw [heq] at this
  simp at this
  exact this

theorem twoTorsionAct_transitive (p : A) (q₁ q₂ : DoublingFiber p) :
    ∃ t : TwoTorsionSet (A := A), twoTorsionActOnFiber p t q₁ = q₂ := by
  refine ⟨⟨q₂.val - q₁.val, ?_⟩, Subtype.ext ?_⟩
  · show q₂.val - q₁.val + (q₂.val - q₁.val) = 0
    have h1 : q₁.val + q₁.val = p := q₁.property
    have h2 : q₂.val + q₂.val = p := q₂.property
    have heq : q₂.val + q₂.val = q₁.val + q₁.val := by rw [h1, h2]
    calc q₂.val - q₁.val + (q₂.val - q₁.val)
        = q₂.val + q₂.val - (q₁.val + q₁.val) := by abel
      _ = q₁.val + q₁.val - (q₁.val + q₁.val) := by rw [heq]
      _ = 0 := sub_self _
  · show q₂.val - q₁.val + q₁.val = q₂.val
    abel

/-! ### Surjectivity and fiber nonemptiness -/

theorem doublingFiber_nonempty_iff (p : A) :
    Nonempty (DoublingFiber p) ↔ ∃ q : A, q + q = p :=
  ⟨fun ⟨⟨q, hq⟩⟩ => ⟨q, hq⟩, fun ⟨q, hq⟩ => ⟨⟨q, hq⟩⟩⟩

theorem doublingMap_surjective_iff :
    Function.Surjective (@doublingMap A _) ↔ ∀ p : A, Nonempty (DoublingFiber p) :=
  ⟨fun h p => let ⟨q, hq⟩ := h p; ⟨⟨q, hq⟩⟩,
   fun h p => let ⟨⟨q, hq⟩⟩ := h p; ⟨q, hq⟩⟩

/-! ### Architecture reading: 2-descent

  | Layer | 2-descent |
  |-------|-----------|
  | Enriched | Points Q with 2Q = P |
  | Bare | The point P |
  | Forgetful | Doubling [2] : A → A |
  | Fiber | Coset of E[2] — 2-torsion torsor |
  | Section | "Halving" — exists iff P in 2A |
  | Obstruction | Class of P in A/2A |

  The quotient A/2A is the starting point of 2-descent for elliptic curves.
  Mathlib's twoTorsionPolynomial characterizes the X-coordinates of 2-torsion points.
-/

end InfinityCompression.GeneralMethod.Descent
