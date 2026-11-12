module

public import TreewidthHom.Incidence
public import TreewidthHom.ColorEncoding

@[expose] public section

namespace TreewidthHom.Relational
variable {R : Type} {arity : R → ℕ} {V W : Type*}

/-- The typed incidence graph with its strictly increasing three-layer rank. -/
def typedDag (A : Relational R arity V) : TypedDag (Tag R arity) A.Vertex where
  edge := A.Edge
  color := A.tag
  rank := A.layer
  increases := A.layer_increases
  separates := A.edge_different_tags

def typedToDagHom {A : Relational R arity V} {B : Relational R arity W}
    (f : TypedHom A B) : TypedDag.Hom A.typedDag B.typedDag :=
  ⟨f.map, f.preserve, f.tags⟩

def dagToTypedHom {A : Relational R arity V} {B : Relational R arity W}
    (f : TypedDag.Hom A.typedDag B.typedDag) : TypedHom A B :=
  ⟨f.map, f.preserve, f.colors⟩

def untypedGraph (A : Relational R arity V) (M : Markers (Tag R arity)) :=
  (A.typedDag.encoded M).assembly.graph

/-- All three schema-erasure stages compose: relational homomorphisms are
exactly homomorphisms of the resulting ordinary simple undirected graphs. -/
theorem relationalReduction_iff (A : Relational R arity V) (B : Relational R arity W)
    (M : Markers (Tag R arity)) :
    Nonempty (A.untypedGraph M →g B.untypedGraph M) ↔ Nonempty (Hom A B) := by
  change Nonempty ((A.typedDag.encoded M).assembly.graph →g
    (B.typedDag.encoded M).assembly.graph) ↔ _
  rw [Digraph.directionReduction_iff (A.typedDag.encoded_noIsolated M),
    TypedDag.colorEncoding_iff]
  constructor
  · rintro ⟨f⟩; exact (dagToTypedHom f).recover
  · rintro ⟨f⟩; exact ⟨typedToDagHom (liftHom f)⟩

end TreewidthHom.Relational
