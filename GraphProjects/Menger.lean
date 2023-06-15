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
open scoped Cardinal

namespace SimpleGraph

def IsSeparator (G : SimpleGraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Path a b, ∃ s ∈ S, s ∈ p.1.support

/-- Definition of a minimal separator of A, B -/
def IsMinSeparator (G : SimpleGraph V) (A B : Set V) (S : Set V)  : Prop := 
  (IsSeparator G A B S) ∧ (∀ T : Set _, IsSeparator G A B T → (# T) ≥ (#S))

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

/-- Definition of a maximal AB-connector -/
def IsMaxConnector (G : SimpleGraph V) (A B : Set V) (C : Connector G A B) : Prop := 
  ∀ D : Connector G A B, (#C.paths) ≥ (#D.paths)

@[simps] --PathBetween for vertex in A ∩ B 
def PathBetween.ofVertex (G : SimpleGraph V) (A B : Set V) (v : V) (h : v ∈ A ∩ B) : G.PathBetween A B where
  first := v
  last := v 
  first_mem := h.1 
  last_mem := h.2 
  path := .nil 

@[simp] -- 
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
    simp [Function.onFun,Walk.interiorSupport_nil] 

lemma Connector_card_eq_card_inter (G : SimpleGraph V) (A B : Set V) : (#(Connector.ofInter A B : Connector G A B).paths) = (#(A ∩ B : Set V)) := by
  apply Cardinal.mk_range_eq 
  intro u v 
  simp  
  exact fun a => SetCoe.ext a 

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


lemma Walk_in_empty_nil (a b : V) (p : (⊥ : SimpleGraph V).Walk a b) : p.length = 0  := by
  cases p 
  rfl
  rename_i ha hp 
  simp at ha 

/-In an empty graph, A ∩ B is an AB-separator.-/
lemma IsSeparator_inter_empty : IsSeparator (⊥ : SimpleGraph V) A B (A ∩ B) := by
  apply IsSeparator_iff.mpr 
  intro a ha b hb p 
  cases p 
  · use a
    simp [ha, hb] 
  · rename_i ha hp 
    simp at ha 



lemma edgeSet_empty_iff (G : SimpleGraph V) : G.edgeSet = ∅ ↔ G = ⊥ := by
  rw [← edgeSet_inj] 
  simp 

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

/-(Should be cleaned up) The number of elements of any separator of A and B is bounded below by |A ∩ B|-/
lemma card_Separator_ge_inter  (G : SimpleGraph V) (h : IsSeparator G A B S) : (#S) ≥ (#(A ∩ B : Set V))  := by
  have : A ∩ B ⊆ S := by 
    intro x hx 
    rw [IsSeparator_iff] at h 
    specialize h x hx.1 x hx.2 
    obtain ⟨s,hs⟩ := h Walk.nil 
    have : x = s := by 
      cases hs.2 
      · trivial
      · tauto 
    rw [← this] at hs   
    exact hs.1 
  exact Cardinal.mk_le_mk_of_subset this

/-Base case for the induction proof: If G has no edges, then there is a connector 
whose number of paths (components) equals the number of elements in a minimal separator-/
lemma base_case (empty : G.edgeSet = ∅) : IsSeparator G A B S ∧ (∀ T : Set _, IsSeparator G A B T → (#T) ≥ (#S)) → ∃ C : Connector G A B, (#C.paths) = (#S) := by 
  intro ⟨hS,hMin⟩ 
  use Connector.ofInter A B 
  rw [Connector_card_eq_card_inter]
  rw [edgeSet_empty_iff] at empty
  have := hMin (A ∩ B)
  rw [empty] at this 
  exact le_antisymm (card_Separator_ge_inter G hS) (this IsSeparator_inter_empty) 

lemma isSeparator_union_singleton (G : SimpleGraph V) (A B S : Set V) (u v : V) 
 (hS : IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A B S) : 
IsSeparator G A B (S ∪ {u}) := by
  classical
  rw [IsSeparator_iff] 
  intro a ha b hb p 
  rw [IsSeparator_iff] at hS
  specialize hS a ha b hb
  have h : ⟦(u,v)⟧ ∈ p.edges ∨ ¬ ⟦(u,v)⟧ ∈ p.edges := by
    exact em (Quotient.mk (Sym2.Rel.setoid V) (u, v) ∈ Walk.edges p)
  cases' h with h1 h2 
  · use u 
    constructor
    · simp
    · apply p.fst_mem_support_of_mem_edges
      exact h1 
  · specialize hS (Walk.toDeleteEdge ⟦(u,v)⟧ p h2) 
    obtain ⟨s,h⟩ := hS
    use s
    constructor
    · left 
      exact h.1 
    · simp at h 
      exact h.2


/- AP separator of G-e is also an AB separator of G -/
  example (G : SimpleGraph V) (A B P S : Set V) (u v : V) (huv: G.Adj u v) (hPS : P = S ∪ {u} ) 
  (hS : IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A B S)
   (hP : IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A P T) : IsSeparator G A B T := by
    classical
    rw [IsSeparator_iff] at * 
    intro a ha b hb p
    specialize hS a ha b hb
    by_cases ⟦(u,v)⟧ ∈ p.edges
    · have : u ∈ p.support := p.fst_mem_support_of_mem_edges h 
      have br : ∃ (q : G.Walk a u) (r : G.Walk u b), p = q.append r := Iff.mp p.mem_support_iff_exists_append this
      rcases br with ⟨q, r⟩ 
      have huP : u ∈ P := by simp [hPS]
      specialize hP a ha u huP


    · sorry

theorem Menger : 
  IsSeparator G A B S ∧ (∀ T : Set _, IsSeparator G A B T → (#T) ≥ (#S)) → 
    ∃ C : Connector G A B, (#C.paths) = (#S) := by sorry
-- example (G : SimpleGraph V) (A B : Set V) (u v : V) (huv: G.Adj u v) (p : G.Walk a b) : 
--   ∃ (q: G.Walk a u), (r: G.Walk u v), (s: G.Walk v b) := by
-- sorry



/-- If G' is obtained from G by removing an edge, then an AB-separator of G is an AB-separator of G'-/
lemma isSeparator_deleted (G : SimpleGraph V) (A B : Set V) (u v : V) (hG : IsSeparator G A B S) : 
IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A B S := by
  rw [IsSeparator_iff] at * 
  intro a ha b hb p 
  have : (∀ (e : Sym2 V), e ∈ Walk.edges p → e ∈ edgeSet G) := by 
    simp [edgeSet_deleteEdges] 
    intro e he 
    have := Walk.edges_subset_edgeSet p he
    rw [edgeSet_deleteEdges] at this 
    exact this.1 
  specialize hG a ha b hb (p.transfer G this) 
  simp [Walk.support_transfer] at hG 
  exact hG

/-- Deleting an edge does not increase the minimum size of a separator. (Can generalize this lemma for larger sets)-/
lemma minSeparator_delete_card_le (G : SimpleGraph V) (A B S T: Set V) (u v : V) (hS : IsSeparator G A B S)
(hT : IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A B T)
(minT : IsMinSeparator (G.deleteEdges {⟦(u,v)⟧}) A B T) : (#T) ≤ (#S) := by
  apply minT.2 
  apply isSeparator_deleted 
  exact hS 

/-- Deleting an edge decrases the minimum size of a separator by at most one.-/
lemma minSeparator_delete_card_atMost (u v : V) (G : SimpleGraph V) (A B S T: Set V) (u v : V) (hS : IsSeparator G A B S)
(hT : IsSeparator (G.deleteEdges {⟦(u,v)⟧}) A B T)
(minT : IsMinSeparator (G.deleteEdges {⟦(u,v)⟧}) A B T) (minS : IsMinSeparator G A B S) :
(#S) ≤ (#T) + 1 := by
  have h : IsSeparator G A B (T ∪ {u}) := isSeparator_union_singleton G A B T u v hT 
  have : (#(T ∪ {u} : Set V)) = (#T) + 1 := by
    sorry
  rw [← this]
  apply minS.2 (T ∪ {u}) 