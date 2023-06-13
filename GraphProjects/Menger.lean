/-
Copyright (c) 2023 by authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Swaroop Hegde, Sung-Yi Liao, Kyle Miller, Jake Weber, Jack Wesley
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.DeriveFintype
import GraphProjects.ForMathlib

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

/-- The vertices of a walk that aren't the start or end. -/
def Walk.interiorSupport {G : SimpleGraph V} : {u v : V} → (p : G.Walk u v) → List V
  | _, _, .nil => []
  | _, _, .cons _ .nil => []
  | _, _, .cons' u v w _ p => v :: p.interiorSupport

theorem Walk.interiorSupport_nil {G : SimpleGraph V} {u : V} :
    (Walk.nil : G.Walk u u).interiorSupport = [] := rfl

theorem Walk.interiorSupport_cons_nil {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    (Walk.cons huv .nil).interiorSupport = [] := rfl

theorem Walk.support_eq_cons_interiorSupport {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hn : ¬ p.length = 0):
    p.support = u :: (p.interiorSupport.concat v) := by
  induction p with
  | nil => simp at hn
  | cons h p ih =>
    cases p with
    | nil => simp [interiorSupport]
    | cons h p => simpa [interiorSupport] using ih

structure Connector (G : SimpleGraph V) (A B : Set V) where
  paths : Set (G.PathBetween A B)
  disjoint : paths.PairwiseDisjoint fun p ↦ {v | v ∈ p.path.1.interiorSupport}

@[simps]
def PathBetween.ofVertex (G : SimpleGraph V) (A B : Set V) (v : V) (h : v ∈ A ∩ B) : G.PathBetween A B where
  first := v
  last := v 
  first_mem := h.1 
  last_mem := h.2 
  path := .nil 

@[simp] 
lemma PathBetween.ofVertex_inj {G : SimpleGraph V} (A B : Set V) (v w : V)
    (hv : v ∈ A ∩ B) (hw : w ∈ A ∩ B) :
    PathBetween.ofVertex G A B v hv = PathBetween.ofVertex G A B w hw ↔ v = w := by
  constructor
  · intro h
    apply_fun PathBetween.first at h
    exact h
  · rintro rfl
    rfl

def Connector.ofInter {G : SimpleGraph V} (A B : Set V) : G.Connector A B where
  paths := Set.range fun v : (A ∩ B : Set V) => PathBetween.ofVertex G A B v v.2
  disjoint := by
    intro p hp q hq
    simp at hp hq
    obtain ⟨v, hv, rfl⟩ := hp
    obtain ⟨w, hw, rfl⟩ := hq 
    simp  
    sorry
    --simp [Function.onFun, Set.disjoint_iff_forall_ne, Set.PairwiseDisjoint]  

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
    (v : V) (hvp : v ∈ p.path.1.interiorSupport) (hvq : v ∈ q.path.1.interiorSupport) :
    p = q := by
  by_contra hpq
  have := C.disjoint hp hq hpq
  rw [Function.onFun, Set.disjoint_iff_forall_ne] at this
  exact this hvp hvq rfl

/-- There are finitely many paths between `A` and `B` in a finite graph. -/
instance [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Set V) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Fintype (G.PathBetween A B) :=
  derive_fintype% (G.PathBetween A B)

instance [Finite V] (G : SimpleGraph V) (A B : Set V) : Finite (G.PathBetween A B) := by
  classical
  have := Fintype.ofFinite V
  infer_instance


open scoped Cardinal

lemma base_case [Finite V] (G : SimpleGraph V) (A B : Set V) (empty : (# G.edgeSet) = 0)  : 1 + 1 = 2:= 
sorry

theorem Menger: 
    IsSeparator G A B S ∧ (∀ T : Set V, (#T) ≥ (#S)) ∨ (¬ IsSeparator G A B T) → 
      ∃ C : Connector G A B, (#C.paths) = (#S) := by 
  sorry