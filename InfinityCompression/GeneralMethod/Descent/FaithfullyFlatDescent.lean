/-
  EPIC_019_GA1 — Faithfully flat descent in the fiber architecture.

  Mathlib proves that injectivity, surjectivity, and bijectivity of ring homomorphisms
  descend along faithfully flat maps. We package this in the positive-closure architecture
  as a **conservative forgetful map**: base change reflects structural properties.

  The architecture reading: the forgetful map (base change along R → S) is not merely
  surjective — it is **conservative** (reflects injectivity, surjectivity, bijectivity).
  This is a stronger form of the positive-closure pattern than the group extension case,
  where the forgetful map is surjective but does not reflect the algebraic section property.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.Logic.Function.Basic

universe u

namespace InfinityCompression.GeneralMethod

/-! ### Architecture bundle: faithfully flat descent reflects properties

For a faithfully flat algebra `R → S`, the base-change functor on ring homomorphisms
reflects injectivity, surjectivity, and bijectivity. This is the descent principle
expressed as a conservative forgetful map in the positive-closure architecture.
-/

theorem faithfullyFlat_reflects_injective :
    RingHom.CodescendsAlong (fun f => Function.Injective f) RingHom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.codescendsAlong_injective

theorem faithfullyFlat_reflects_surjective :
    RingHom.CodescendsAlong (fun f => Function.Surjective f) RingHom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.codescendsAlong_surjective

theorem faithfullyFlat_reflects_bijective :
    RingHom.CodescendsAlong (fun f => Function.Bijective f) RingHom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.codescendsAlong_bijective

/-! ### Architecture reading

  | Layer | Content |
  |-------|---------|
  | Enriched | Ring homomorphism `f : R → T` |
  | Bare | Base-changed map `S → S ⊗[R] T` |
  | Forgetful | Base change along faithfully flat `R → S` |
  | Property fiber | Injective / surjective / bijective |
  | Descent | Properties descend: bare property implies enriched property |

  This is a **conservative** instance of the architecture: the forgetful map reflects
  all three fundamental properties. Compare with group extensions, where the forgetful
  map (quotient homomorphism) is surjective but does NOT reflect the splitting property
  (a set-theoretic section always exists, but a homomorphic one may not).

  The two cases together demonstrate the architecture's range:
  - **Group extensions:** forgetful map is surjective; enriched property (splitting)
    requires additional algebraic structure (trivial cocycle).
  - **Faithfully flat descent:** forgetful map is conservative; enriched properties
    are fully determined by bare properties.
-/

end InfinityCompression.GeneralMethod
