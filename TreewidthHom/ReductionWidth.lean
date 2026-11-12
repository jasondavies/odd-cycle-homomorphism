module

public import TreewidthHom.IncidenceWidth
public import TreewidthHom.LCSTargetWidth

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- A supplied tree-decomposition certificate of width at most w. -/
def HasWidth {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop := by
  exact ∃ d : DecidableEq V, ∃ B : Type, ∃ T : SimpleGraph B, ∃ D : @Decomposition V B d G T,
    ∀ b, (D.bag b).card ≤ w+1

theorem HasWidth.mono {V : Type} {G : SimpleGraph V} {a b : ℕ}
    (h : HasWidth G a) (hab : a ≤ b) : HasWidth G b := by
  obtain ⟨d,B,T,D,hw⟩ := h
  exact ⟨d,B,T,D,fun c => (hw c).trans (Nat.add_le_add_right hab 1)⟩

/-- All three encodings preserve a supplied width bound up to the fixed gadget constant. -/
theorem UnaryBinary.untyped_width {V : Type} (A : UnaryBinary V) {w : ℕ}
    (h : HasWidth A.gaifman w) :
    HasWidth (A.asRelational.untypedGraph schemaMarkers) (max w 12) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := h
  let := d
  have ha : ∀ r, Relational.schemaArity r ≤ 2 := by
    intro r; unfold Relational.schemaArity; split <;> omega
  obtain ⟨T1,D1,h1⟩ := A.asRelational.incidence_width D ha (A.fact_bag D) hw
  obtain ⟨T2,D2,h2⟩ := A.asRelational.typedDag.colorEncoding_width schemaMarkers D1 h1
  obtain ⟨T3,D3,h3⟩ := (A.asRelational.typedDag.encoded schemaMarkers).directionReduction_width D2 h2
  refine ⟨inferInstance,_,T3,D3,?_⟩
  intro b
  have hb := h3 b
  omega

namespace LCSInstance

theorem source_width (k N ℓ : ℕ) : HasWidth (sourceGraph k N ℓ) (max (2*k) 12) := by
  classical
  exact (query k N ℓ).untyped_width ⟨inferInstance,_,_,queryDecomposition k N ℓ,query_width k N ℓ⟩

theorem final_target_width {k : ℕ} (words : Fin k → List Bool) :
    HasWidth (targetGraph words) 12 := by
  obtain ⟨B,T,D,hw⟩ := target_width words
  have h : HasWidth (target words).gaifman 4 := ⟨inferInstance,B,T,D,hw⟩
  exact (target words).untyped_width h

/-- The concrete reduction, with both treewidth certificates. -/
theorem lcs_bounded_graph_reduction {k N ℓ : ℕ} (words : Fin k → List Bool)
    (hN : ∀ i, (words i).length ≤ N) :
    (Nonempty (sourceGraph k N ℓ →g targetGraph words) ↔ CommonSubsequence words ℓ) ∧
    HasWidth (sourceGraph k N ℓ) (max (2*k) 12) ∧ HasWidth (targetGraph words) 12 :=
  ⟨lcs_graph_iff words hN,source_width k N ℓ,final_target_width words⟩

end LCSInstance
end TreewidthHom
