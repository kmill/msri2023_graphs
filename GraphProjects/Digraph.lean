import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite


open Finset Function

universe u v w

/-- A directed graph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
-/
@[ext]
structure Digraph (V : Type u) where
  Adj : V → V → Prop

noncomputable instance {V : Type u} [Fintype V] : Fintype (Digraph V) := by
  classical exact Fintype.ofInjective Digraph.Adj Digraph.ext

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def Digraph.completeGraph (V : Type u) : Digraph V where Adj := ⊤ 

/-- The graph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def Digraph.emptyGraph (V : Type u) : Digraph V where Adj _ _ := False


namespace Digraph

variable {ι : Sort _} {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : Digraph V)
  (G' : Digraph W) {a b c u v w : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) :=
  Digraph.ext

@[simp]
theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

section Order

/-- The relation that one `Digraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Sup (Digraph V) where
  sup x y :=
    { Adj := x.Adj ⊔ y.Adj }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (Digraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance hasCompl : HasCompl (Digraph V) where
  compl G :=
    { Adj := fun v w => ¬G.Adj v w }

@[simp]
theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s :=
    { Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by
  simp [iInf]

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { show DistribLattice (Digraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeBooleanAlgebra : CompleteBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w _ => trivial
    bot_le := fun x v w h => h.elim
    sdiff_eq := fun x y => by
      ext (v w)
      exact Iff.rfl
    inf_compl_le_bot := fun G v w h => False.elim <| h.2 h.1
    top_le_sup_compl := fun G v w _ => by
      by_cases G.Adj v w
      · exact Or.inl h
      · exact Or.inr h
    sSup := sSup
    le_sSup := fun s G hG a b hab => ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b => by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab => hab hG
    le_sInf := fun s G hG a b hab => fun H hH => hG _ hH hab
    inf_sSup_le_iSup_inf := fun G s a b hab => by simpa using hab
    iInf_sup_le_sup_sInf := fun G s a b hab => by
      simpa [forall_and, forall_or_left, or_and_right] using hab }

@[simp]
theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp]
theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type u) : Inhabited (Digraph V) :=
  ⟨⊥⟩

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

end Decidable

end Order

-- /-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
-- def neighborSet (v : V) : Set V := {w | G.Adj v w}
-- #align simple_graph.neighbor_set Digraph.neighborSet

-- instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
--     DecidablePred (· ∈ G.neighborSet v) :=
--   inferInstanceAs <| DecidablePred (Adj G v)
-- #align simple_graph.neighbor_set.mem_decidable Digraph.neighborSet.memDecidable

section EdgeSet

variable {G₁ G₂ : Digraph V}

/-- The edges of G consist of the ordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`Digraph.edgeSet`.
-/
def edgeSetEmbedding (V : Type _) : Digraph V ↪o Set (V × V) :=
  OrderEmbedding.ofMapLEIff (fun G => {e | G.Adj e.1 e.2}) fun _ _ =>
    ⟨fun h a b => @h (a, b), fun h _ h' => h h'⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : Digraph V) : Set (V × V) := edgeSetEmbedding V G

@[simp]
theorem mem_edgeSet : (v, w) ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl

theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ :=
  (edgeSetEmbedding V).le_iff_le

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ :=
  (edgeSetEmbedding V).lt_iff_lt

theorem edgeSet_injective : Injective (edgeSet : Digraph V → Set (V × V)) :=
  (edgeSetEmbedding V).injective

alias edgeSet_subset_edgeSet ↔ _ edgeSet_mono

alias edgeSet_ssubset_edgeSet ↔ _ edgeSet_strict_mono

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
theorem edgeSet_bot : (⊥ : Digraph V).edgeSet = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  simp

@[simp]
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  fun x => inferInstanceAs <| Decidable (G.Adj x.1 x.2)

instance fintypeEdgeSet [Fintype V] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _

instance fintypeEdgeSetBot : Fintype (⊥ : Digraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

end EdgeSet


/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `Digraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (V × V)) : Digraph V
    where
  Adj x y := G.Adj x y ∧ ¬ (x, y) ∈ s

@[simp]
theorem deleteEdges_adj (s : Set (V × V)) (v w : V) :
    (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬(v, w) ∈ s :=
  Iff.rfl

theorem sdiff_eq_deleteEdges (G G' : Digraph V) : G \ G' = G.deleteEdges G'.edgeSet := by
  ext
  simp

theorem compl_eq_deleteEdges : Gᶜ = (⊤ : Digraph V).deleteEdges G.edgeSet := by
  ext
  simp
#align simple_graph.compl_eq_delete_edges Digraph.compl_eq_deleteEdges

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (V × V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by
  ext
  simp [and_assoc, not_or]
  
@[simp]
theorem deleteEdges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  simp

@[simp]
theorem deleteEdges_univ_eq : G.deleteEdges Set.univ = ⊥ := by
  ext
  simp

theorem deleteEdges_le (s : Set (V × V)) : G.deleteEdges s ≤ G := by
  intro
  simp (config := { contextual := true })


theorem deleteEdges_le_of_le {s s' : Set (V × V)} (h : s ⊆ s') :
    G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [deleteEdges_adj, and_imp, true_and_iff]
  exact fun _ hn hs => hn (h hs)

theorem deleteEdges_eq_inter_edgeSet (s : Set (V × V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp (config := { contextual := true }) [imp_false]

theorem deleteEdges_sdiff_eq_of_le {H : Digraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext (v w)
  constructor <;> simp (config := { contextual := true }) [@h v w]

theorem edgeSet_deleteEdges (s : Set (V × V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e
  cases e
  simp


/-! ## Map and comap -/


/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `Digraph.map_injective`). -/
protected def map (f : V → W) (G : Digraph V) : Digraph W where
  Adj := Relation.Map G.Adj f f

@[simp]
theorem map_adj (f : V → W) (G : Digraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

theorem map_monotone (f : V → W) : Monotone (Digraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `Digraph.induce` for a wrapper.

This is surjective when `f` is injective (see `Digraph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : Digraph V where
  Adj u v := G.Adj (f u) (f v)

theorem comap_monotone (f : V → W) : Monotone (Digraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : Digraph V) : (G.map f).comap f = G := by
  ext
  simp

theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (Digraph.comap f) (Digraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (Digraph.map f) :=
  (leftInverse_comap_map f).injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (Digraph.comap f) :=
  (leftInverse_comap_map f).surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : Digraph V) (G' : Digraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V ↪ W) (G : Digraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `Digraph V` and `Digraph s`.

There is also a notion of induced subgraphs (see `Digraph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `Digraph.comap`. -/
@[reducible]
def induce (s : Set V) (G : Digraph V) : Digraph s :=
  G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `Digraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `Digraph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : Digraph s) : Digraph V :=
  G.map (Function.Embedding.subtype _)

theorem induce_spanningCoe {s : Set V} {G : Digraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _


section Maps

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
#align simple_graph.hom Digraph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
#align simple_graph.embedding Digraph.Embedding

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj
#align simple_graph.iso Digraph.Iso

-- mathport name: «expr →g »
infixl:50 " →g " => Hom

-- mathport name: «expr ↪g »
infixl:50 " ↪g " => Embedding

-- mathport name: «expr ≃g »
infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbrev id : G →g G :=
  RelHom.id _
#align simple_graph.hom.id Digraph.Hom.id

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
#align simple_graph.hom.map_adj Digraph.Hom.map_adj

theorem map_mem_edgeSet {e : V × V} (h : e ∈ G.edgeSet) : e.map f f ∈ G'.edgeSet := by
  cases e
  exact f.map_rel' h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Prod.map f f e, f.map_mem_edgeSet e.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : Digraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha
#align simple_graph.hom.map_spanning_subgraphs Digraph.Hom.mapSpanningSubgraphs

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat' rw [Subtype.mk_eq_mk]
  cases e₁
  cases e₂
  simp
  intro h1 h2
  simp [hinj h1, hinj h2]

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `Digraph.Embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : Digraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp
#align simple_graph.hom.comap Digraph.Hom.comap

variable {G'' : Digraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f
#align simple_graph.hom.comp Digraph.Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.hom.coe_comp Digraph.Hom.coe_comp

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _
#align simple_graph.embedding.refl Digraph.Embedding.refl

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom
#align simple_graph.embedding.to_hom Digraph.Embedding.toHom

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.embedding.map_adj_iff Digraph.Embedding.map_adj_iff

theorem map_mem_edgeSet_iff {e : V × V} : e.map f f ∈ G'.edgeSet ↔ e ∈ G.edgeSet := by
  cases e
  simp [f.map_adj_iff]

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.injective
#align simple_graph.embedding.map_edge_set Digraph.Embedding.mapEdgeSet

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ↪ W) (G : Digraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.comap Digraph.Embedding.comap

@[simp]
theorem comap_apply (f : V ↪ W) (G : Digraph W) (v : V) :
  Digraph.Embedding.comap f G v = f v := rfl
#align simple_graph.embedding.comap_apply Digraph.Embedding.comap_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: @[simps] does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ↪ W) (G : Digraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.map Digraph.Embedding.map

@[simp]
theorem map_apply (f : V ↪ W) (G : Digraph V) (v : V) :
  Digraph.Embedding.map f G v = f v := rfl
#align simple_graph.embedding.map_apply Digraph.Embedding.map_apply

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  Digraph.Embedding.comap (Function.Embedding.subtype _) G
#align simple_graph.embedding.induce Digraph.Embedding.induce

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : Digraph s) : G ↪g G.spanningCoe :=
  Digraph.Embedding.map (Function.Embedding.subtype _) G
#align simple_graph.embedding.spanning_coe Digraph.Embedding.spanningCoe

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ↪ β) :
    (⊤ : Digraph α) ↪g (⊤ : Digraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.embedding.complete_graph Digraph.Embedding.completeGraph

variable {G'' : Digraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'
#align simple_graph.embedding.comp Digraph.Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.embedding.coe_comp Digraph.Embedding.coe_comp

end Embedding

section InduceHom

variable {G G'} {G'' : Digraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def InduceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'
#align simple_graph.induce_hom Digraph.InduceHom

@[simp, norm_cast] lemma coe_induceHom : ⇑(InduceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl
#align simple_graph.coe_induce_hom Digraph.coe_induceHom

@[simp] lemma induceHom_id (G : Digraph V) (s) :
    InduceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl
#align simple_graph.induce_hom_id Digraph.induceHom_id

@[simp] lemma induceHom_comp :
    (InduceHom ψ ψtr).comp (InduceHom φ φst) = InduceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl
#align simple_graph.induce_hom_comp Digraph.induceHom_comp

end InduceHom

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _
#align simple_graph.iso.refl Digraph.Iso.refl

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding
#align simple_graph.iso.to_embedding Digraph.Iso.toEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom
#align simple_graph.iso.to_hom Digraph.Iso.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G :=
  RelIso.symm f
#align simple_graph.iso.symm Digraph.Iso.symm

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
#align simple_graph.iso.map_adj_iff Digraph.Iso.map_adj_iff

theorem map_mem_edgeSet_iff {e : V × V} : e.map f f ∈ G'.edgeSet ↔ e ∈ G.edgeSet := by
  cases e
  simp [f.map_adj_iff]

-- /-- An isomorphism of graphs induces an equivalence of edge sets. -/
-- @[simps]
-- def mapEdgeSet : G.edgeSet ≃ G'.edgeSet
--     where
--   toFun := Hom.mapEdgeSet f
--   invFun := Hom.mapEdgeSet f.symm
--   left_inv := by
--     rintro ⟨e, h⟩
--     cases e
--     simp [Hom.mapEdgeSet, Prod.map_map, RelEmbedding.toRelHom]
--     convert congr_fun Sym2.map_id e
--     exact RelIso.symm_apply_apply _ _
--   right_inv := by
--     rintro ⟨e, h⟩
--     simp [Hom.mapEdgeSet, Sym2.map_map, RelEmbedding.toRelHom]
--     convert congr_fun Sym2.map_id e
--     exact RelIso.apply_symm_apply _ _
-- #align simple_graph.iso.map_edge_set Digraph.Iso.mapEdgeSet

theorem card_eq_of_iso [Fintype V] [Fintype W] (f : G ≃g G') : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  -- porting note: need to help it to find the typeclass instances from the target expression
  apply @Fintype.card_congr' _ _ (_) (_) rfl
#align simple_graph.iso.card_eq_of_iso Digraph.Iso.card_eq_of_iso

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
protected def comap (f : V ≃ W) (G : Digraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.comap Digraph.Iso.comap

@[simp]
lemma comap_apply (f : V ≃ W) (G : Digraph W) (v : V) :
  Digraph.Iso.comap f G v = f v := rfl
#align simple_graph.iso.comap_apply Digraph.Iso.comap_apply

@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : Digraph W) (w : W) :
  (Digraph.Iso.comap f G).symm w = f.symm w := rfl
#align simple_graph.iso.comap_symm_apply Digraph.Iso.comap_symm_apply

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
protected def map (f : V ≃ W) (G : Digraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.map Digraph.Iso.map

@[simp]
lemma map_apply (f : V ≃ W) (G : Digraph V) (v : V) :
  Digraph.Iso.map f G v = f v := rfl
#align simple_graph.iso.map_apply Digraph.Iso.map_apply

@[simp]
lemma map_symm_apply (f : V ≃ W) (G : Digraph V) (w : W) :
  (Digraph.Iso.map f G).symm w = f.symm w := rfl
#align simple_graph.iso.map_symm_apply Digraph.Iso.map_symm_apply

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ≃ β) :
    (⊤ : Digraph α) ≃g (⊤ : Digraph β) :=
  { f with map_rel_iff' := by simp }
#align simple_graph.iso.complete_graph Digraph.Iso.completeGraph

theorem toEmbedding_completeGraph {α β : Type _} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl
#align simple_graph.iso.to_embedding_complete_graph Digraph.Iso.toEmbedding_completeGraph

variable {G'' : Digraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'
#align simple_graph.iso.comp Digraph.Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
#align simple_graph.iso.coe_comp Digraph.Iso.coe_comp

end Iso

end Maps

end Digraph
