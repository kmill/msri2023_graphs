/-
Copyright (c) 2023 by authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Swaroop Hegde, Sung-Yi Liao, Kyle Miller, Jake Weber, Jack Wesley
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-! # Menger's theorem for simple graphs

Following the proof in [...]
-/

namespace SimpleGraph

def IsSeparator (G : SimpleGraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Path a b, ∃ s ∈ S, s ∈ p.1.support

structure PathBetween (G : SimpleGraph V) (A B : Set V) where
  (first last : V)
  (first_mem : first ∈ A)
  (last_mem : last ∈ B)
  (path : G.Path first last)

structure Connector (G : SimpleGraph V) (A B : Set V) where
  paths : Set (G.PathBetween A B)
  disjoint : paths.PairwiseDisjoint fun p ↦ {v | v ∈ p.path.1.support}

/-- Separators via `Path` is the same as separators via `Walk`. -/
lemma IsSeparator_iff :
    IsSeparator G A B S ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ s ∈ S, s ∈ p.support := by
  classical
  constructor
  · intro hs a ha b hb p
    obtain ⟨s, hs, hsp⟩ := hs a ha b hb p.toPath
    use s, hs
    exact Walk.support_toPath_subset _ hsp
  · intro hs a ha b hb p
    exact hs a ha b hb p

/-- Another characterization of the disjointness axiom of a connector. -/
lemma Connector.disjoint' {G : SimpleGraph V} (C : G.Connector A B)
    (p q : G.PathBetween A B) (hp : p ∈ C.paths) (hq : q ∈ C.paths)
    (v : V) (hvp : v ∈ p.path.1.support) (hvq : v ∈ q.path.1.support) :
    p = q := by
  by_contra hpq
  have := C.disjoint hp hq hpq
  rw [Function.onFun, Set.disjoint_iff_forall_ne] at this
  exact this hvp hvq rfl
  
