/-
  EPIC 013 — `CompressionArchitecture` + linear chain embedding (`toArchitecture`).

  Paths are edge lists `(a,b) ∈ edges`; acyclicity is “no duplicate nodes on any edge-walk”.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

import InfinityCompression.Meta.CompressionChain

universe u

namespace InfinityCompression.Meta

open InfinityCompression.Core

variable {BD : Type u}

/-- Consecutive pairs in `path` must be directed edges in `edges`. -/
def pathUsesEdges {α : Type*} (edges : List (α × α)) (path : List α) : Prop :=
  match path with
  | [] | [_] => True
  | a :: b :: rest => (a, b) ∈ edges ∧ pathUsesEdges edges (b :: rest)

/-- Def 13.5 — finite DAG-shaped architecture (acyclicity as “no duplicate nodes on edge-paths”). -/
structure CompressionArchitecture (BurdenDesc : Type u) (n : ℕ) where
  nodes : Fin n → CompressionInstance BurdenDesc
  edges : List (Fin n × Fin n)
  acyclic : ∀ path : List (Fin n), pathUsesEdges edges path → path.Nodup
  terminal : Fin n

private theorem val_lt_n (n : ℕ) (hn : 0 < n) (i : Fin (n - 1)) : i.val < n :=
  Nat.lt_trans i.is_lt (Nat.pred_lt (Nat.ne_of_gt hn))

private theorem val_succ_lt_n (n : ℕ) (hn : 0 < n) (i : Fin (n - 1)) : i.val + 1 < n :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt i.is_lt) (Nat.pred_lt (Nat.ne_of_gt hn))

/-- Forward edges `(k, k+1)` for `k = 0 … n-2` (linear DAG on `Fin n`). -/
def linearChainEdges (n : ℕ) (hn : 0 < n) : List (Fin n × Fin n) :=
  List.ofFn fun i : Fin (n - 1) => (⟨i.val, val_lt_n n hn i⟩, ⟨i.val + 1, val_succ_lt_n n hn i⟩)

private theorem lt_of_mem_linear {n : ℕ} (hn : 0 < n) {a b : Fin n}
    (h : (a, b) ∈ linearChainEdges n hn) : a.val < b.val := by
  simp only [linearChainEdges, List.mem_ofFn] at h
  rcases h with ⟨i, rfl, rfl⟩
  exact Nat.lt_succ_self i.val

private theorem all_gt_head_of_pathUses {n : ℕ} (hn : 0 < n) (a b : Fin n) (rest : List (Fin n))
    (hp : pathUsesEdges (linearChainEdges n hn) (a :: b :: rest)) :
    ∀ x ∈ b :: rest, a.val < x.val := by
  induction rest generalizing a b with
  | nil =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | htail
    · exact lt_of_mem_linear hn hp.1
    · simp at htail
  | cons c rest ih =>
    intro x hx
    cases hx with
    | head => exact lt_of_mem_linear hn hp.1
    | tail _ hx' =>
      have hp' : pathUsesEdges (linearChainEdges n hn) (b :: c :: rest) := hp.2
      have ha_lt_b : a.val < b.val := lt_of_mem_linear hn hp.1
      rcases List.mem_cons.mp hx' with rfl | hxr
      · exact Nat.lt_trans ha_lt_b (lt_of_mem_linear hn hp'.1)
      · exact Nat.lt_trans ha_lt_b (ih b c hp' x (List.mem_cons_of_mem c hxr))

private theorem nodup_of_pathUses_linear {n : ℕ} (hn : 0 < n) (path : List (Fin n))
    (hp : pathUsesEdges (linearChainEdges n hn) path) : path.Nodup := by
  classical
  match path with
  | [] => simp [List.nodup_nil]
  | [_] => simp
  | a :: b :: rest =>
    have hrest : pathUsesEdges (linearChainEdges n hn) (b :: rest) := hp.2
    have hgt : ∀ x ∈ b :: rest, a.val < x.val := all_gt_head_of_pathUses hn a b rest hp
    have ha : a ∉ b :: rest := by
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Nat.lt_irrefl _ (lt_of_mem_linear hn hp.1)
      · exact Nat.lt_irrefl _ (hgt _ (List.mem_cons_of_mem _ htail))
    refine List.nodup_cons.mpr ⟨ha, nodup_of_pathUses_linear hn (b :: rest) hrest⟩

/-- Def 13.6 — canonical linear architecture from a nonempty list length. -/
def CompressionChain.toArchitecture {BD : Type u} (ch : CompressionChain BD) :
    CompressionArchitecture BD ch.steps.length where
  nodes := fun i => ch.steps.get ⟨i, i.is_lt⟩
  edges := linearChainEdges ch.steps.length (List.length_pos_of_ne_nil ch.nonempty)
  acyclic := nodup_of_pathUses_linear (List.length_pos_of_ne_nil ch.nonempty)
  terminal := ⟨ch.steps.length - 1, Nat.pred_lt (List.length_pos_of_ne_nil ch.nonempty).ne'⟩

end InfinityCompression.Meta
