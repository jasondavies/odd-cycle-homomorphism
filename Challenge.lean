module

public import Mathlib

@[expose] public section

/-!
# List elimination into odd-cycle homomorphism

This independent statement imports only Mathlib. All custom notions used below
are defined here: ordinary tree/path decompositions, their minimum widths,
feedback vertex number, and degeneracy. Widths are nonnegative, including for
empty graphs. The theorem's graph is finite, so the minima are attained.

The claim is the finite mathematical reduction and its structural upper bounds,
not a formal complexity-class theorem. `Solution.lean` supplies the concrete
reference-cycle construction and proves the statement using the development.
No statement definition is left unspecified; only the final proof is omitted.
The manuscript's matching lower bounds, binary-encoding reduction, core
recognition, and machine resource analysis remain outside this formal claim.
-/

namespace TreewidthHom
open SimpleGraph

/-- A tree decomposition over a specified tree of bags. -/
structure Decomposition {V B : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph B) where
  tree : T.IsTree
  bag : B → Finset V
  vertex_cover : ∀ v, ∃ b, v ∈ bag b
  edge_cover : ∀ {u v}, G.Adj u v → ∃ b, u ∈ bag b ∧ v ∈ bag b
  running : ∀ v a b, v ∈ bag a → v ∈ bag b →
    ∃ p : T.Walk a b, ∀ c ∈ p.support, v ∈ bag c

/-- A supplied tree-decomposition certificate of width at most w. -/
def HasWidth {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop := by
  exact ∃ d : DecidableEq V, ∃ B : Type, ∃ T : SimpleGraph B, ∃ D : @Decomposition V B d G T,
    ∀ b, (D.bag b).card ≤ w+1

/-- A supplied path-decomposition certificate of width at most w. -/
def HasPathWidth {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop := by
  exact ∃ d : DecidableEq V, ∃ n : ℕ,
    ∃ D : @Decomposition V (Fin (n+1)) d G (pathGraph (n+1)), ∀ b, (D.bag b).card ≤ w+1

/-- The least width of a tree decomposition. -/
noncomputable def treewidth {V : Type} (G : SimpleGraph V) : ℕ := sInf {w | HasWidth G w}

/-- The least width of a path decomposition. -/
noncomputable def pathwidth {V : Type} (G : SimpleGraph V) : ℕ := sInf {w | HasPathWidth G w}

/-- The least size of a set of vertices whose deletion leaves an acyclic graph. -/
noncomputable def fvs {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ (G.induce {v | v ∉ S}).IsAcyclic}

/-- Every nonempty finite set of vertices contains a vertex with at most `k`
neighbours in the set. -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, ∃ N : Finset V, N.card ≤ k ∧ ∀ u ∈ S, G.Adj v u → u ∈ N

/-- Every finite List Colouring instance over an odd residue palette has an
ordinary graph-homomorphism encoding with additive structural overhead.
The same witness satisfies both certificate transfers and numerical bounds.
`egirth` is the length of a shortest cycle, or infinity for a forest.
The connectedness premise holds for padded palettes; exact girth needs a
nonempty input. The polynomial bound counts vertices, not machine resources. -/
theorem Palomar.list_elimination {m n : ℕ} (F : SimpleGraph (Fin m))
    (L : Fin m → Finset (ZMod n)) (hodd : Odd n) (hn : 5 ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod n))) ↔
        ∃ c : Fin m → ZMod n, (∀ v, c v ∈ L v) ∧
          ∀ u v, F.Adj u v → c u ≠ c v) ∧
      (∀ w, HasWidth F w → HasWidth G (max (w+2) 3)) ∧
      (∀ p, HasPathWidth F p → HasPathWidth G (p+6)) ∧
      HasPathWidth (circulantGraph {1} : SimpleGraph (ZMod n)) 2 ∧
      (∀ S : Finset (Fin m), (F.induce {v | v ∉ S}).IsAcyclic →
        ∃ S' : Finset V, S'.card = S.card+2 ∧
          (G.induce {v | v ∉ S'}).IsAcyclic) ∧
      treewidth G ≤ max (treewidth F + 2) 3 ∧
      pathwidth G ≤ pathwidth F + 6 ∧
      fvs G ≤ fvs F + 2 ∧
      IsDegenerate G 2 ∧
      (n : ℕ∞) ≤ G.egirth ∧
      (0 < m → G.egirth = n) ∧
      ((∀ v, ∃ d, d ∉ L v) → G.Connected) ∧
      Nat.card V ≤ 2+m+m*n*n+(m*n+m*m)*n ∧
      Nat.card G.edgeSet ≤ 2*Nat.card V ∧
      ((∀ v, ((n-1 : ℕ) : ZMod n) ∉ L v) →
        (0 < m → treewidth F + 2 ≤ treewidth G ∧ pathwidth F + 2 ≤ pathwidth G) ∧
        ((∃ u v, F.Adj u v) → treewidth G = treewidth F + 2 ∧ fvs G = fvs F + 2)) ∧
      (∀ k, 5 ≤ k →
        (Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod k))) ↔
          Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod (min k (2*Fintype.card V+5))))))) ∧
      (0 < m →
        ((∃ k, 3 ≤ k ∧ Odd k ∧
          Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod k))) ∧
          Nonempty ((circulantGraph {1} : SimpleGraph (ZMod k)) →g G)) ↔
        ∃ c : Fin m → ZMod n, (∀ v, c v ∈ L v) ∧
          ∀ u v, F.Adj u v → c u ≠ c v)) := by
  sorry

end TreewidthHom
