module

public import TreewidthHom.ConeDecomposition
public import TreewidthHom.DecompositionMaps

@[expose] public section

namespace TreewidthHom

/-- Attach one finite parent chain for each index, rooted at a chosen old vertex. -/
def chainGraft {V I : Type*} (root : I → V) (length : I → ℕ) :
    RootedGraft V (Σ i, Fin (length i)) where
  parent p := if h : p.2.val = 0 then Sum.inl (root p.1)
    else Sum.inr ⟨p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩⟩
  height p := p.2.val
  decreases := by
    intro p q h
    by_cases hp : p.2.val = 0
    · simp [hp] at h
    · simp only [dite_eq_right hp] at h
      have hv := congrArg (fun x : Σ i, Fin (length i) => x.2.val) (Sum.inr.inj h)
      dsimp only at hv ⊢
      omega
  root p := root p.1
  root_parent := by intro p; split <;> rfl

end TreewidthHom
