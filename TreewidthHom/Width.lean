module

public import TreewidthHom.TreeDecomposition

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

end TreewidthHom
