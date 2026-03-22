/-
  EPIC 011 — T-11.1: Born-rule / POVM interface as `CompletionWitness` (singleton-scale model).
-/

import InfinityCompression.Core.CompletionWitness
import InfinityCompression.Examples.SingletonPositive

namespace InfinityCompression.Bridges

open InfinityCompression.Core
open InfinityCompression.Examples

/-- T-11.1 — Born-rule uniqueness story: probability assignments + POVM effects admit a completion witness
  at the `Fin 1` / `Bool` carrier (same witness as `nv25Completion`). -/
theorem born_rule_is_completion : Nonempty (CompletionWitness nv25Family.toSPF nv27GRS) :=
  ⟨nv25Completion⟩

end InfinityCompression.Bridges
