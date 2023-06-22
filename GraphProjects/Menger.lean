/-
Copyright (c) 2023 by authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Swaroop Hegde, Sung-Yi Liao, Kyle Miller, Jake Weber, Jack Wesley
-/

import GraphProjects.DigraphConnectivity
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.DeriveFintype 
import GraphProjects.ForMathlib
import GraphProjects.DigraphInduction


/-! # Menger's theorem for simple graphs

Following the proof in [...]
-/
open scoped Cardinal

namespace Digraph

def IsSeparator (G : Digraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Path a b, ∃ s ∈ S, s ∈ p.1.support

/-- Definition of a minimal separator of A, B -/
def IsMinSeparator (G : Digraph V) (A B : Set V) (S : Set V)  : Prop := 
  (IsSeparator G A B S) ∧ (∀ T : Set _, IsSeparator G A B T → (# T) ≥ (#S))

structure PathBetween (G : Digraph V) (A B : Set V) where
  (first last : V)
  (first_mem : first ∈ A)
  (last_mem : last ∈ B)
  (path : G.Path first last)

-- def PathBetween.reverse {G : Digraph V} {A B : Set V} (p : G.PathBetween A B) :
--     G.PathBetween B A where
--   first := p.last
--   last := p.first
--   first_mem := p.last_mem
--   last_mem := p.first_mem
--   path := p.path.reverse 



/-- The vertices of a walk that aren't the start or end. -/
def Walk.interiorSupport {G : Digraph V} : {u v : V} → (p : G.Walk u v) → List V
  | _, _, .nil => []
  | _, _, .cons _ .nil => []
  | _, _, .cons' u v w _ p => v :: p.interiorSupport

theorem Walk.interiorSupport_nil {G : Digraph V} {u : V} :
    (Walk.nil : G.Walk u u).interiorSupport = [] := rfl

theorem Walk.interiorSupport_cons_nil {G : Digraph V} {u v : V} (huv : G.Adj u v) :
    (Walk.cons huv .nil).interiorSupport = [] := rfl

theorem Walk.support_eq_cons_interiorSupport {G : Digraph V} {u v : V} (p : G.Walk u v) (hn : ¬ p.length = 0):
    p.support = u :: (p.interiorSupport.concat v) := by
  induction p with 
  | nil => simp at hn
  | cons h p ih =>
    cases p with
    | nil => simp [interiorSupport]
    | cons h p => simpa [interiorSupport] using ih

lemma IsSeparator.comm {G : Digraph V} {A B : Set V} {S : Set V}
    (hs : IsSeparator G A B S) : IsSeparator G B A S := sorry

structure Connector (G : Digraph V) (A B : Set V) where
  paths : Set (G.PathBetween A B)
  disjoint : paths.PairwiseDisjoint fun p ↦ {v | v ∈ p.path.1.support}
  disjointAB : ∀ p ∈ paths, (A ∪ B) ∩ {v | v ∈ p.path.1.interiorSupport} = ∅ 

def Connector.reverse {G : Digraph V} {A B : Set V} (C : G.Connector A B) :
    G.Connector B A where
  paths := sorry
  disjoint := sorry
  disjointAB := sorry

/-- Definition of a maximal AB-connector -/
def IsMaxConnector (G : Digraph V) (A B : Set V) (C : Connector G A B) : Prop := 
  ∀ D : Connector G A B, (#C.paths) ≥ (#D.paths)

@[simps] --PathBetween for vertex in A ∩ B 
def PathBetween.ofVertex (G : Digraph V) (A B : Set V) (v : V) (h : v ∈ A ∩ B) : G.PathBetween A B where
  first := v
  last := v 
  first_mem := h.1 
  last_mem := h.2 
  path := .nil 

@[simp] -- 
lemma PathBetween.ofVertex_inj {G : Digraph V} (A B : Set V) (v w : V)
    (hv : v ∈ A ∩ B) (hw : w ∈ A ∩ B) :
    PathBetween.ofVertex G A B v hv = PathBetween.ofVertex G A B w hw ↔ v = w := by
  constructor
  · intro h
    apply_fun PathBetween.first at h
    exact h
  · rintro rfl
    rfl
 
def Connector.ofInter {G : Digraph V} (A B : Set V) : G.Connector A B where
  paths := Set.range fun v : (A ∩ B : Set V) => PathBetween.ofVertex G A B v v.2
  disjoint := by
    intro p hp q hq
    simp at hp hq
    obtain ⟨v, hv, rfl⟩ := hp
    obtain ⟨w, hw, rfl⟩ := hq 
    simp [Function.onFun,Walk.interiorSupport_nil] 
  disjointAB := by 
    intro p hP 
    simp [Function.onFun] at hP 
    obtain ⟨v,⟨hv,h⟩⟩ := hP  
    rw [← h] 
    simp [Walk.interiorSupport_nil] 

lemma Connector_card_eq_card_inter (G : Digraph V) (A B : Set V) : (#(Connector.ofInter A B : Connector G A B).paths) = (#(A ∩ B : Set V)) := by
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

--Need to fix hypotheses: Add p1 : G.PathBetween A S p2: G.PathBetween A S p1.last ≠ p2.last -> p1,p2 disjoint
def PathBetween.append_fromSeparator [DecidableEq V] {G : Digraph V} {A B : Set V}
 (hS : IsSeparator G A B S) (p : G.PathBetween A S) (q : G.PathBetween S B) 
 (h : p.last = q.first) (pintOnce : {v | v ∈ p.path.1.support} ∩ S = {p.last}) 
 (qintOnce : {v | v ∈ q.path.1.support} ∩ S = {q.first}) : 
  G.PathBetween A B where
  first := p.first
  last := q.last
  first_mem := p.first_mem
  last_mem := q.last_mem
  path := ⟨Walk.append (p.path.1.copy rfl h) q.path.1 , by 
    have : {v | v ∈ p.path.1.support} ∩ {v | v ∈ q.path.1.support} = {p.last} := by
      ext
      constructor
      · intro h 
        simp at h 
        apply Set.mem_singleton_iff.mpr 
        by_contra 
        rename_i v hv 
        let r := Walk.takeUntil p.path.1 v h.1 
        let s := Walk.dropUntil q.path.1 v h.2 
        let rs := Walk.append r s 
        rw [IsSeparator_iff] at hS  
        specialize hS p.first p.first_mem q.last q.last_mem rs 
        obtain ⟨w,hw⟩ := hS 
        have h' : w = p.last := by
          sorry
      
        sorry
      · sorry
      sorry

    rw [Walk.isPath_def] 
    simp 
    --rw [Walk.mem_support_append_iff.2]
    sorry⟩ 


lemma Walk_in_empty_nil (a b : V) (p : (⊥ : Digraph V).Walk a b) : p.length = 0  := by
  cases p 
  rfl
  rename_i ha hp 
  simp at ha 

/-In an empty graph, A ∩ B is an AB-separator.-/
lemma IsSeparator_inter_empty : IsSeparator (⊥ : Digraph V) A B (A ∩ B) := by
  apply IsSeparator_iff.mpr 
  intro a ha b hb p 
  cases p 
  · use a
    simp [ha, hb] 
  · rename_i ha hp 
    simp at ha 



lemma edgeSet_empty_iff (G : Digraph V) : G.edgeSet = ∅ ↔ G = ⊥ := by
  rw [← edgeSet_inj] 
  simp 

/-- Another characterization of the disjointness axiom of a connector. -/
lemma Connector.disjoint' {G : Digraph V} (C : G.Connector A B)
    (p q : G.PathBetween A B) (hp : p ∈ C.paths) (hq : q ∈ C.paths)
    (v : V) (hvp : v ∈ p.path.1.support) (hvq : v ∈ q.path.1.support) :
    p = q := by 
  by_contra hpq
  have := C.disjoint hp hq hpq
  rw [Function.onFun, Set.disjoint_iff_forall_ne] at this 
  exact this hvp hvq rfl 

-- /-- There are finitely many paths between `A` and `B` in a finite graph. -/
-- instance [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
--     (A B : Set V) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
--     Fintype (G.PathBetween A B) :=
--   derive_fintype% (G.PathBetween A B)

-- instance [Finite V] (G : Digraph V) (A B : Set V) : Finite (G.PathBetween A B) := by
--   classical
--   have := Fintype.ofFinite V
--   infer_instance

/-(Should be cleaned up) The number of elements of any separator of A and B is bounded below by |A ∩ B|-/
lemma card_Separator_ge_inter  (G : Digraph V) (h : IsSeparator G A B S) : (#S) ≥ (#(A ∩ B : Set V))  := by
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

lemma isSeparator_union_singleton (G : Digraph V) (A B S : Set V) (u v : V) 
 (hS : IsSeparator (G.deleteEdges {(u,v)}) A B S) : 
IsSeparator G A B (S ∪ {u}) := by
  classical
  rw [IsSeparator_iff] 
  intro a ha b hb p 
  rw [IsSeparator_iff] at hS
  specialize hS a ha b hb
  have h : (u,v) ∈ p.edges ∨ ¬ (u,v) ∈ p.edges := by
    exact em _ 
  cases' h with h1 h2 
  · use u 
    constructor
    · simp
    · apply p.fst_mem_support_of_mem_edges
      exact h1 
  · specialize hS (Walk.toDeleteEdge (u,v) p h2) 
    obtain ⟨s,h⟩ := hS
    use s
    constructor
    · left 
      exact h.1 
    · simp at h 
      exact h.2

/- An edge on a walk in G-e is an edge in G. -/
lemma edge_transfer_from_DeleteEdge (G: Digraph V) (m : V × V) (p: Path (G.deleteEdges {m}) s t): 
  ∀ e , e ∈ p.1.edges → e ∈ G.edgeSet := by 
  intro e he
  have := p.1.edges_subset_edgeSet he
  have G'_le_G :=  deleteEdges_le G {m}
  exact edgeSet_subset_edgeSet.2 G'_le_G this
  
  --exact G.deleteEdges_le {⟦(u,v)⟧}

lemma aux (G : Digraph V) (p : G.Path u v) (h : (v, x) ∈ p.1.edges) : False := by
  obtain ⟨p, hp⟩ := p
  induction p
  · simp at h
  · simp at h
    obtain (⟨rfl, rfl⟩ | h) := h
    · simp at hp
    · simp at hp
      rename_i ih
      exact ih hp.1 h

lemma takeUntil_of_first_nil [DecidableEq V] 
{u : V} {G : Digraph V} (p : Walk G u v) {h : u ∈ p.support} : p.takeUntil u h  = Walk.nil := by
  cases p 
  · rfl  
  · rename_i v ha q 
    unfold Walk.takeUntil 
    simp 

/--In a digraph, if (u,v) is an edge in a path p, 
then the path taken up to u does not contain the edge (u,v).-/
lemma takeUntil_support_no_edge [DecidableEq V] {G : Digraph V} {u v : V} {p : Walk G a b} (h : u ∈ p.support) 
    (he : (u,v) ∈ p.edges) : (u,v) ∉ (p.takeUntil u h).edges := by
  have := Walk.count_edges_takeUntil_eq_zero p h v 
  apply List.count_eq_zero.mp 
  convert this
  ext ⟨v, w⟩ ⟨v', w'⟩
  simp [BEq.beq]

/--Old/incomplete/bad proof; will remove once above 'sorry' is fixed-/
lemma takeUntil_support_no_edge' [DecidableEq V] {G : Digraph V} {u v : V} {p : Walk G a b} (h : u ∈ p.support) 
(he : (u,v) ∈ p.edges) : (u,v) ∉ (p.takeUntil u h).edges := by
  induction p with
  | nil =>  
    simp at he 
  | cons a q ih =>    
    simp at *  
    cases' he with heq h2 
    rename_i x y z 
    · --have qq := Walk.edges_copy (Walk.takeUntil (Walk.cons a q) u h) heq.1.symm rfl 
      have : Walk.copy (Walk.takeUntil (Walk.cons a q) u h) heq.1.symm rfl  = Walk.nil := by 
        have hxu := heq.1.symm
        have hzz : z = z := by rfl 
        rw [← Walk.takeUntil_copy (Walk.cons a q) hxu hzz (by 
          simp 
          left
          exact heq.1 
          )] 
        rw [takeUntil_of_first_nil (Walk.copy (Walk.cons a q) hxu hzz)] 
      rw [← Walk.edges_copy (Walk.takeUntil (Walk.cons a q) u h) heq.1.symm rfl] 
      rw [this] 
      simp  
    · intro hu   
      have : u ∈ Walk.support q := by
        sorry
      specialize ih this h2     
      apply ih 
      unfold Walk.takeUntil  
      sorry

lemma deleteEdges_support_eq {G : Digraph V} {a b: V} {p : Walk G a b} {s : Set _}
{hp : ∀ e, e ∈ p.edges → ¬ e ∈ s} : 
  p.support = (Walk.toDeleteEdges s p hp).support := by
  simp  

/--An AP separator of G-e is also an AB separator of G -/
example (G : Digraph V) (A B P S : Set V) (u v : V) (huv: G.Adj u v) (hPS : P = S ∪ {u} ) 
  (hS : IsSeparator (G.deleteEdges {(u,v)}) A B S)
   (hP : IsSeparator (G.deleteEdges {(u,v)}) A P T) : IsSeparator G A B T := by
  classical
  have G' := G.deleteEdges {(u,v)}
  rw [IsSeparator_iff] at * 
  intro a ha b hb p 
  specialize hS a ha b hb
  by_cases (u,v) ∈ p.edges
  · have uinp : u ∈ p.support := p.fst_mem_support_of_mem_edges h   
    specialize hP a ha u (by simp [hPS])
    have hp : ∀ (e : V × V), e ∈ Walk.edges (Walk.takeUntil p u uinp) → ¬ (e ∈ ({(u,v)} : Set _)) := by  
      intro e he
      simp 
      intro euv
      have := takeUntil_support_no_edge uinp h 
      rw [euv] at he 
      exact this he
    let q : Walk (deleteEdges G {(u, v)}) a u := 
    (Walk.toDeleteEdges {(u,v)} (Walk.takeUntil p u uinp) hp) 
    specialize hP q 
    obtain ⟨s,hs⟩ := hP 
    use s
    constructor
    · exact hs.1 
    · apply Walk.support_takeUntil_subset p uinp   
      have : Walk.support q = Walk.support (Walk.takeUntil p u uinp) := by
        simp
      rw [this] at hs
      exact hs.2
  · let p_inG' := p.toDeleteEdge (u,v) h
    specialize hS p_inG'
    rcases hS with ⟨ s, ⟨sinS, s_in_S_ab_G'_supp⟩⟩ 
    let ⟨q, r, hp⟩ := Iff.mp Walk.mem_support_iff_exists_append s_in_S_ab_G'_supp
    have s_inP : s ∈ P := by simp [sinS, hPS]
    specialize hP a ha s s_inP q
    rcases hP with ⟨  s1, ⟨s1_in_T, s1_in_q_support⟩ ⟩ 
    use s1, s1_in_T
    have : s1 ∈ q.support ∨ s1 ∈ r.support := Or.inl s1_in_q_support
    have s1_in_append_p_in_G': s1 ∈ (Walk.append q r).support :=  (Walk.mem_support_append_iff q r).2 this
    rw [Eq.symm hp] at s1_in_append_p_in_G'
    simp only [Walk.support_transfer] at s1_in_append_p_in_G'
    exact s1_in_append_p_in_G' 
  
theorem Menger : 
  IsSeparator G A B S ∧ (∀ T : Set _, IsSeparator G A B T → (#T) ≥ (#S)) → 
    ∃ C : Connector G A B, (#C.paths) = (#S) := by sorry
-- example (G : Digraph V) (A B : Set V) (u v : V) (huv: G.Adj u v) (p : G.Walk a b) : 
--   ∃ (q: G.Walk a u), (r: G.Walk u v), (s: G.Walk v b) := by
-- sorry


lemma setCardAddOneMem (T : Set V) (u : V) (h: ¬ u ∈ T) : (#(T ∪ {u} : Set V)) = (#T) + 1 := by
  have disjoint: Disjoint T {u} := by
    simpa
    -- rw [Set.disjoint_iff]
    -- rintro x ⟨hx, rfl⟩ 
    -- contradiction

  rw [ Cardinal.mk_union_of_disjoint disjoint]
  simp only [Cardinal.mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one]

lemma setCardAddOneMem' (T : Set V) (u : V) (h: u ∈ T) : (#(T ∪ {u} : Set V)) = (#T) := by
  simp only [Set.union_singleton, Set.insert_eq_of_mem h]


/-- If G' is obtained from G by removing an edge, then an AB-separator of G is an AB-separator of G'-/
lemma isSeparator_deleted (G : Digraph V) (A B : Set V) (u v : V) (hG : IsSeparator G A B S) : 
IsSeparator (G.deleteEdges {(u,v)}) A B S := by
  rw [IsSeparator_iff] at * 
  intro a ha b hb p 
  have : (∀ (e : V × V), e ∈ Walk.edges p → e ∈ edgeSet G) := by 
    intro e he 
    have := Walk.edges_subset_edgeSet p he
    rw [edgeSet_deleteEdges] at this 
    exact this.1 
  specialize hG a ha b hb (p.transfer G this) 
  simp [Walk.support_transfer] at hG 
  exact hG

/-- Deleting an edge does not increase the minimum size of a separator. (Can generalize this lemma for larger sets)-/
lemma minSeparator_delete_card_le (G : Digraph V) (A B S T: Set V) (u v : V) (hS : IsSeparator G A B S)
(hT : IsSeparator (G.deleteEdges {(u,v)}) A B T)
(minT : IsMinSeparator (G.deleteEdges {(u,v)}) A B T) : (#T) ≤ (#S) := by
  apply minT.2 
  apply isSeparator_deleted 
  exact hS 

/-- Deleting an edge decreases the minimum size of a separator by at most one.-/
lemma minSeparator_delete_card_atMost (u v : V) (G : Digraph V) (A B S T: Set V) (u v : V) (hS : IsSeparator G A B S)
(hT : IsSeparator (G.deleteEdges {(u,v)}) A B T)
-- (minT : IsMinSeparator (G.deleteEdges {⟦(u,v)⟧}) A B T) 
(minS : IsMinSeparator G A B S) 
(hu: ¬ u ∈ T):
(#S) ≤ (#T) + 1 := by 
  have h : IsSeparator G A B (T ∪ {u}) := isSeparator_union_singleton G A B T u v hT 
  have : (#(T ∪ {u} : Set V)) = (#T) + 1 := by
    apply setCardAddOneMem T u hu
  rw [← this]
  apply minS.2 (T ∪ {u}) 
  exact h
