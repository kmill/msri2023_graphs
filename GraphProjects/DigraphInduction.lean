import GraphProjects.Digraph

namespace Digraph

@[elab_as_elim]
theorem deleteEdges_induction [Finite V] {motive : Digraph V → Prop}
    (hbot : motive ⊥)
    (hdelete : ∀ (G : Digraph V) (v w : V), G.Adj v w → motive (G.deleteEdges {(v, w)}) → motive G)
    (G : Digraph V) : motive G := by
  classical
  have : Fintype V := Fintype.ofFinite V
  generalize hs : G.edgeSet.toFinset = s
  induction s using Finset.induction generalizing G with
  | empty =>
    rw [← Set.toFinset_empty, Set.toFinset_inj, ← edgeSet_bot, edgeSet_inj] at hs
    rwa [hs]
  | @insert e s he ih =>
    have : e ∈ G.edgeSet
    · rw [← Set.mem_toFinset, hs]
      exact Finset.mem_insert_self e s
    apply hdelete G e.1 e.2 this
    apply ih
    ext ⟨v, w⟩
    simp only [Prod.mk.eta, Set.mem_toFinset, mem_edgeSet, deleteEdges_adj, Set.mem_singleton_iff]
    apply_fun ((v, w) ∈ ·) at hs
    simp only [Set.mem_toFinset, mem_edgeSet, Finset.mem_insert, eq_iff_iff] at hs 
    rw [hs]
    constructor
    · rintro ⟨(rfl | ha), hne⟩
      · simp at hne
      · assumption
    · intro h
      simp only [h, or_true, true_and]
      rintro rfl
      exact absurd h he
