module

public import TreewidthHom.MinorModel

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Join a graph to a clique on the apex type. -/
def apexJoin {V A : Type} (G : SimpleGraph V) : SimpleGraph (V ⊕ A) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr a, .inr b => a ≠ b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := ⟨by rintro (u | u) (v | v) h; exact h.symm; trivial; trivial; exact h.symm⟩
  loopless := ⟨by rintro (u | a) h; exact G.loopless.irrefl u h; exact h rfl⟩

abbrev twoApex {V : Type} (G : SimpleGraph V) : SimpleGraph (V ⊕ Fin 2) := apexJoin G

end TreewidthHom
