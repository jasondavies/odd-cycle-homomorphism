module

public import TreewidthHom.LCSDecode
public import TreewidthHom.LCSEncode

@[expose] public section

namespace TreewidthHom.LCSInstance

/-- Correctness of the actual six-relation construction, for all lengths and
all numbers of strings (including zero). -/
theorem lcs_relational_iff {k N ℓ : ℕ} (words : Fin k → List Bool)
    (hN : ∀ i, (words i).length ≤ N) :
    Nonempty (UnaryBinary.Hom (query k N ℓ) (target words)) ↔ CommonSubsequence words ℓ := by
  constructor
  · rintro ⟨f⟩
    by_cases hk : 0 < k
    · exact Decode.commonSubsequence f hk
    · have he : k = 0 := by omega
      subst k
      refine ⟨List.replicate ℓ false,by simp,fun i => Fin.elim0 i⟩
  · exact commonSubsequence_hom hN

/-- The final simple undirected source graph, with all labels and directions erased. -/
noncomputable def sourceGraph (k N ℓ : ℕ) :=
  (query k N ℓ).asRelational.untypedGraph schemaMarkers

/-- The final simple undirected target graph. -/
noncomputable def targetGraph {k : ℕ} (words : Fin k → List Bool) :=
  (target words).asRelational.untypedGraph schemaMarkers

/-- End-to-end decision equivalence, from standard LCS to ordinary simple graphs.
Width and complexity bounds are separate obligations. -/
theorem lcs_graph_iff {k N ℓ : ℕ} (words : Fin k → List Bool)
    (hN : ∀ i, (words i).length ≤ N) :
    Nonempty (sourceGraph k N ℓ →g targetGraph words) ↔ CommonSubsequence words ℓ := by
  unfold sourceGraph targetGraph
  rw [Relational.relationalReduction_iff, ← UnaryBinary.hom_iff_relational]
  exact lcs_relational_iff words hN

end TreewidthHom.LCSInstance
