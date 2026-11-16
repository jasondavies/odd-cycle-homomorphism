module

public import TreewidthHom.GraftTree

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Deleting vertices whose complement has decreasing parent pointers leaves
an acyclic graph. -/
theorem acyclic_of_apex_forest {V : Type} (G : SimpleGraph V) (hub : V → Prop)
    (parent : {v // ¬ hub v} → Option {v // ¬ hub v}) (height : {v // ¬ hub v} → ℕ)
    (hdec : ∀ p q, parent p = some q → height q < height p)
    (hedge : ∀ p q : {v // ¬ hub v}, G.Adj p.val q.val → parent p = some q ∨ parent q = some p) :
    (G.induce {v | ¬ hub v}).IsAcyclic := by
  classical
  let F : Graft Unit {v // ¬ hub v} :=
    { parent := fun p => (parent p).elim (.inl ()) .inr
      height := height
      decreases := by
        intro p q h
        cases hp : parent p with
        | none => simp [hp] at h
        | some r =>
          have hr : r = q := by simpa [hp] using h
          subst hr
          exact hdec p r hp }
  let f : G.induce {v | ¬ hub v} →g F.graph (⊥ : SimpleGraph Unit) :=
    { toFun := fun v => Sum.inr v
      map_rel' := by
        intro u v h
        rcases hedge u v h with hp | hp
        · exact Or.inl (by simp [F,hp])
        · exact Or.inr (by simp [F,hp]) }
  have hinj : Function.Injective f := fun u v h => Sum.inr.inj h
  have hF : (F.graph (⊥ : SimpleGraph Unit)).IsAcyclic :=
    F.acyclic ⊥ (IsTree.of_subsingleton (G := (⊥ : SimpleGraph Unit))).isAcyclic
  intro v p hp
  exact hF (p.map f) (hp.map hinj)

end TreewidthHom
