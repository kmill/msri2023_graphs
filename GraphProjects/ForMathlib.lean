import Mathlib.Combinatorics.SimpleGraph.Connectivity

namespace SimpleGraph

instance fintypeSetPathLength' {V : Type _} (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (u v : V) (n : ℕ) : Fintype {p : G.Path u v | p.1.length = n} :=
  Fintype.ofEquiv {p : G.Walk u v | p.IsPath ∧ p.length = n}
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Fintype (G.Path x y) where
  elems := (Finset.range (Fintype.card V)).biUnion fun n =>
    Set.toFinset {p : G.Path x y | p.1.length = n}
  complete := by simp [Walk.IsPath.length_lt]
