/-
  EPIC 013 — chain composition theorems (T-13.1–T-13.4) + architecture aggregates (T-13.6, T-13.7).
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

import InfinityCompression.Meta.CompressionArchitecture

universe u

namespace InfinityCompression.Meta

open InfinityCompression.Core

variable {BD : Type u}

/-- Disjunctive aggregation over finitely many nodes (Def 13.4 style). -/
def CompressionArchitecture.aggregateProfile {n : ℕ} (A : CompressionArchitecture BD n) :
    CompressionProfile :=
  { hasFiniteCharacterization := ∃ i : Fin n, (A.nodes i).profile.hasFiniteCharacterization
    hasVerificationReduction := ∃ i : Fin n, (A.nodes i).profile.hasVerificationReduction
    hasTransferConcentration := ∃ i : Fin n, (A.nodes i).profile.hasTransferConcentration
    hasRepresentationEconomy := ∃ i : Fin n, (A.nodes i).profile.hasRepresentationEconomy
    hasUniformity := ∃ i : Fin n, (A.nodes i).profile.hasUniformity }

private theorem append_compatible {ch₁ ch₂ : CompressionChain BD}
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    ∀ i : Fin ((ch₁.steps ++ ch₂.steps).length - 1),
      ((ch₁.steps ++ ch₂.steps).get ⟨i.val, by
        have hpos : 0 < (ch₁.steps ++ ch₂.steps).length := by
          have := List.length_pos_of_ne_nil ch₁.nonempty
          have := List.length_pos_of_ne_nil ch₂.nonempty
          simp [List.length_append]
          omega
        have := i.is_lt
        omega⟩).target =
        ((ch₁.steps ++ ch₂.steps).get ⟨i.val + 1, by
        have hpos : 0 < (ch₁.steps ++ ch₂.steps).length := by
          have := List.length_pos_of_ne_nil ch₁.nonempty
          have := List.length_pos_of_ne_nil ch₂.nonempty
          simp [List.length_append]
          omega
        have := i.is_lt
        omega⟩).source := by
  intro i
  let as := ch₁.steps
  let bs := ch₂.steps
  let L₁ := as.length
  let L₂ := bs.length
  have hL₁ : 0 < L₁ := List.length_pos_of_ne_nil ch₁.nonempty
  have hL₂ : 0 < L₂ := List.length_pos_of_ne_nil ch₂.nonempty
  have hlen : (as ++ bs).length = L₁ + L₂ := @List.length_append _ as bs
  by_cases hlt : i.val < L₁ - 1
  · have hi₁ : i.val < L₁ := by omega
    have hi₁' : i.val + 1 < L₁ := by omega
    have hget₀ : (as ++ bs)[i.val]'(by omega) = as[i.val]'hi₁ := List.getElem_append_left hi₁
    have hget₁ : (as ++ bs)[i.val + 1]'(by omega) = as[i.val + 1]'hi₁' :=
      List.getElem_append_left hi₁'
    have hcomp := ch₁.compatible ⟨i.val, by omega⟩
    simp only [List.get_eq_getElem] at hcomp ⊢
    rw [hget₀, hget₁] at ⊢
    exact hcomp
  · by_cases hb : i.val = L₁ - 1
    · -- boundary: last of `as` ↔ head of `bs`
      have hget₀ : (as ++ bs)[L₁ - 1]'(by omega) = as[L₁ - 1]'(by omega) :=
        List.getElem_append_left (by omega)
      have hget₁ : (as ++ bs)[L₁]'(by omega) = bs[0]'(by omega) := by
        rw [List.getElem_append_right (show L₁ ≤ L₁ from Nat.le_refl _)]
        have hL : L₁ = as.length := rfl
        simp [hL]
      have hlast : as[L₁ - 1]'(by omega) = as.getLast ch₁.nonempty := by
        rw [List.getLast_eq_getElem]
      have hhead : bs[0]'(by omega) = bs.head ch₂.nonempty := by
        rw [List.head_eq_getElem]
      rw [← hlast, ← hhead] at hjoin
      have hidx : L₁ - 1 + 1 = L₁ := Nat.succ_pred_eq_of_pos hL₁
      simp only [List.get_eq_getElem] at ⊢
      simp [hb, hidx] at ⊢
      rw [hget₀, hget₁] at ⊢
      exact hjoin
    · have hi₂ : L₁ ≤ i.val := by omega
      let j : ℕ := i.val - L₁
      have hj : j < L₂ - 1 := by
        have hi' : i.val < L₁ + L₂ - 1 := by simpa [hlen] using i.is_lt
        omega
      have hget₀ : (as ++ bs)[i.val]'(by omega) = bs[j]'(by omega) := by
        rw [List.getElem_append_right hi₂]
      have hidx_succ : i.val + 1 - L₁ = j + 1 := by
        dsimp [j]
        omega
      have hget₁ : (as ++ bs)[i.val + 1]'(by omega) = bs[j + 1]'(by omega) := by
        have hle : L₁ ≤ i.val + 1 := by omega
        rw [List.getElem_append_right hle]
        simp [hidx_succ, show as.length = L₁ from rfl]
      have hcomp := ch₂.compatible ⟨j, by
        have hi' : i.val < L₁ + L₂ - 1 := by simpa [hlen] using i.is_lt
        omega⟩
      simp only [List.get_eq_getElem] at hcomp ⊢
      rw [hget₀, hget₁] at ⊢
      exact hcomp

/-- Concatenate two chains when the last source/target interface matches. -/
def CompressionChain.append (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    CompressionChain BD where
  steps := ch₁.steps ++ ch₂.steps
  nonempty := List.append_ne_nil_of_right_ne_nil ch₁.steps ch₂.nonempty
  compatible := fun i => append_compatible hjoin i

/-- T-13.1 — compatible chains concatenate to a chain. -/
theorem chain_composition (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    ∃ ch : CompressionChain BD, ch.steps = ch₁.steps ++ ch₂.steps :=
  ⟨CompressionChain.append ch₁ ch₂ hjoin, rfl⟩

/-- T-13.2 — if some step is nontrivial, the aggregate profile gains TC or VR. -/
theorem chain_aggregate_nontrivial (ch : CompressionChain BD)
    (h : ∃ s, s ∈ ch.steps ∧ (s.profile.hasTransferConcentration ∨ s.profile.hasVerificationReduction)) :
    ch.aggregateProfile.hasTransferConcentration ∨
      ch.aggregateProfile.hasVerificationReduction := by
  rcases h with ⟨s, hs, hn⟩
  rcases hn with htc | hvr
  · left
    exact ⟨s, hs, htc⟩
  · right
    exact ⟨s, hs, hvr⟩

/-- T-13.3 — singleton embedding into `CompressionChain`. -/
theorem chain_embedding (step : CompressionInstance BD) :
    ∃ ch : CompressionChain BD, ch.steps = [step] ∧ ch = CompressionInstance.singletonChain step := by
  refine ⟨CompressionInstance.singletonChain step, ?_, rfl⟩
  simp [CompressionInstance.singletonChain]

/-- T-13.4 — every chain yields an architecture via `toArchitecture`. -/
theorem chain_to_architecture (ch : CompressionChain BD) :
    ∃ A : CompressionArchitecture BD ch.steps.length, A = ch.toArchitecture :=
  ⟨ch.toArchitecture, rfl⟩

/-- T-13.5 — composing compatible chains yields a composed linear architecture (canonical DAG glue).

  Packaging uses the composed `CompressionChain` `ch` so the node count `ch.steps.length` matches
  `CompressionArchitecture BD ch.steps.length` definitionally (nested `∃ n, ∃ A : … n` would not
  unify in Lean without `Sigma`/`cast`). -/
theorem architecture_composition (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    ∃ ch : CompressionChain BD,
      ch = CompressionChain.append ch₁ ch₂ hjoin ∧
        ch.steps.length = ch₁.steps.length + ch₂.steps.length ∧
          ∃ A : CompressionArchitecture BD ch.steps.length, A = ch.toArchitecture :=
  let ch := CompressionChain.append ch₁ ch₂ hjoin
  ⟨ch, rfl, by simp [ch, CompressionChain.append, List.length_append], ch.toArchitecture, rfl⟩

/-- Length of appended compression chains (for dependent-type alignment in T-13.5 spec form). -/
theorem append_chain_steps_length (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    (CompressionChain.append ch₁ ch₂ hjoin).steps.length = ch₁.steps.length + ch₂.steps.length := by
  simp [CompressionChain.append, List.length_append]

/-- T-13.5 (spec shape) — nested `∃ n, ∃ A : CompressionArchitecture BD n` packaging the composed
  architecture as a `Sigma.mk` equal to the canonical transport of `toArchitecture` along
  `append_chain_steps_length` (written `h ▸ ·`, i.e. `Eq.rec`).

  For the usual `cast (congrArg (CompressionArchitecture BD) …)` prose form, use the same transport:
  it is definitionally `Eq.rec` / `▸` on the `ℕ`-indexed family; see also `architecture_composition_toArchitecture_heq`. -/
theorem architecture_composition_spec (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    ∃ n : ℕ, ∃ A : CompressionArchitecture BD n,
      n = ch₁.steps.length + ch₂.steps.length ∧
        Sigma.mk n A =
          Sigma.mk (ch₁.steps.length + ch₂.steps.length)
            ((append_chain_steps_length ch₁ ch₂ hjoin) ▸ (CompressionChain.append ch₁ ch₂ hjoin).toArchitecture) := by
  let ch := CompressionChain.append ch₁ ch₂ hjoin
  let hlen := append_chain_steps_length ch₁ ch₂ hjoin
  let arch : CompressionArchitecture BD (ch₁.steps.length + ch₂.steps.length) := hlen ▸ ch.toArchitecture
  let p : Σ (len : ℕ), CompressionArchitecture BD len :=
    @Sigma.mk ℕ (fun len => CompressionArchitecture BD len) (ch₁.steps.length + ch₂.steps.length) arch
  exact ⟨p.1, p.2, And.intro rfl rfl⟩

/-- Same composition as a single dependent pair (avoids repeating the `cast` in the statement). -/
theorem architecture_composition_spec_sigma (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    ∃ (p : Σ (len : ℕ), CompressionArchitecture BD len),
      p =
        @Sigma.mk ℕ (fun len => CompressionArchitecture BD len) (ch₁.steps.length + ch₂.steps.length)
          ((append_chain_steps_length ch₁ ch₂ hjoin) ▸ (CompressionChain.append ch₁ ch₂ hjoin).toArchitecture) :=
  let ch := CompressionChain.append ch₁ ch₂ hjoin
  let hlen := append_chain_steps_length ch₁ ch₂ hjoin
  Exists.intro
    (@Sigma.mk ℕ (fun len => CompressionArchitecture BD len) (ch₁.steps.length + ch₂.steps.length) (hlen ▸ ch.toArchitecture))
    rfl

/-- `cast` along the length lemma is heterogeneously equal to the underlying `toArchitecture`. -/
theorem architecture_composition_toArchitecture_heq (ch₁ ch₂ : CompressionChain BD)
    (hjoin : (ch₁.steps.getLast ch₁.nonempty).target = (ch₂.steps.head ch₂.nonempty).source) :
    HEq
      (cast (congrArg (CompressionArchitecture BD) (append_chain_steps_length ch₁ ch₂ hjoin))
        (CompressionChain.append ch₁ ch₂ hjoin).toArchitecture)
      (CompressionChain.append ch₁ ch₂ hjoin).toArchitecture :=
  cast_heq _ _

/-- T-13.6 — any nontrivial node forces aggregate TC/VR. -/
theorem architecture_aggregate_nontrivial {n : ℕ} (A : CompressionArchitecture BD n)
    (h : ∃ i : Fin n,
      (A.nodes i).profile.hasTransferConcentration ∨
        (A.nodes i).profile.hasVerificationReduction) :
    A.aggregateProfile.hasTransferConcentration ∨
      A.aggregateProfile.hasVerificationReduction := by
  rcases h with ⟨i, hi⟩
  rcases hi with htc | hvr
  · left
    exact ⟨i, htc⟩
  · right
    exact ⟨i, hvr⟩

/-- T-13.7 — one-node architecture from a single step (canonical linear case). -/
theorem singleton_architecture (step : CompressionInstance BD) :
    (CompressionInstance.singletonChain step).toArchitecture.nodes = fun _ : Fin 1 => step := by
  funext i
  fin_cases i
  simp [CompressionChain.toArchitecture, CompressionInstance.singletonChain]

end InfinityCompression.Meta
