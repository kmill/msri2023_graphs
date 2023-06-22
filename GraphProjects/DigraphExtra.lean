import GraphProjects.Digraph

namespace Digraph

/-- Constructor for directed graphs using a boolean-valued function. -/
@[simps]
protected def mk' :
    (V → V → Bool) ↪ Digraph V where
  toFun f := ⟨fun v w ↦ f v w⟩
  inj' := by
    rintro adj adj'
    rw [mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_bool_iff] using congr_fun₂ h v w

instance {V : Type u} [Fintype V] [DecidableEq V] : Fintype (Digraph V) where
  elems := Finset.univ.map Digraph.mk'
  complete := by
    classical
    rintro ⟨Adj⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    refine ⟨fun v w ↦ Adj v w, ?_⟩
    ext
    simp

theorem le_iff_eq_deleteEdges {G G' : Digraph V} :
    G ≤ G' ↔ ∃ s, s ⊆ G'.edgeSet ∧ G = G'.deleteEdges s := by
  constructor
  · intro h
    use G'.edgeSet \ G.edgeSet
    refine ⟨Set.diff_subset _ _, ?_⟩
    ext v w
    simp only [deleteEdges_adj, Set.mem_diff, mem_edgeSet, not_and, not_not]
    constructor <;> simp (config := {contextual := true}) [@h v w]
  · rintro ⟨s, _, rfl⟩
    apply deleteEdges_le

-- I'm sure this could be cleaner
theorem lt_iff_eq_deleteEdges {G G' : Digraph V} :
    G < G' ↔ ∃ (s : Set (V × V)), s.Nonempty ∧ s ⊆ G'.edgeSet ∧ G = G'.deleteEdges s := by
  constructor
  · intro h
    use G'.edgeSet \ G.edgeSet
    constructor
    · by_contra hn
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty, edgeSet_subset_edgeSet] at hn
      exact lt_irrefl _ (trans h hn)
    constructor
    · apply Set.diff_subset
    · ext v w
      simp only [deleteEdges_adj, Set.mem_diff, mem_edgeSet, not_and, not_not]
      have : G.Adj v w → G'.Adj v w := fun e => h.le e
      constructor <;> simp (config := {contextual := true}) [this]
  · rintro ⟨s, ⟨⟨v, w⟩, h⟩, hs, rfl⟩
    rw [lt_iff_le_and_ne]
    constructor
    · apply deleteEdges_le
    · intro hd
      apply_fun (Adj · v w) at hd
      have := hs h
      rw [mem_edgeSet] at this
      simp [this, h] at hd