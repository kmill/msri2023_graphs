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

/-- `deleteEdges_induction` in terms of adding edges instead of deleting them. -/
@[elab_as_elim]
theorem deleteEdges_induction' [Finite V] {motive : Digraph V → Prop}
    (hbot : motive ⊥)
    (hdelete : ∀ (G : Digraph V) (v w : V), ¬ G.Adj v w → motive G → motive (G ⊔ (edgeSetIso V).symm {(v, w)}))
    (G : Digraph V) : motive G := by
  induction G using deleteEdges_induction with
  | hbot => exact hbot
  | hdelete G v w hvw ih =>
    convert hdelete (G.deleteEdges {(v, w)}) v w (by simp) ih
    ext a b
    simp only [Set.le_eq_subset, ge_iff_le, sup_adj, deleteEdges_adj, Set.mem_singleton_iff, Prod.mk.injEq, not_and]
    rw [edgeSetIso_symm_adj]
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · tauto
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h.1
      · assumption

/-- Note: DigraphExtra has `lt_iff_eq_deleteEdges` which might be useful when applying this. -/
@[elab_as_elim]
protected theorem strong_induction [Finite V] {motive : Digraph V → Prop}
    (hind : ∀ G : Digraph V, (∀ G', G' < G → motive G') → motive G)
    (G : Digraph V) : motive G := by
  classical
  have : Fintype V := Fintype.ofFinite V
  generalize hs : G.edgeSet.toFinset = s
  induction s using Finset.strongInduction generalizing G with
  | _ s ih =>
    cases hs
    apply hind
    intros G' hG
    exact ih G'.edgeSet.toFinset (by simpa using hG) _ rfl
