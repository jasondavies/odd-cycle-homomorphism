module

public import Mathlib

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Attach any family of fresh leaves to selected vertices of a graph. -/
def leafTree {B E : Type*} (T : SimpleGraph B) (parent : E → B) : SimpleGraph (B ⊕ E) where
  Adj
    | .inl u, .inl v => T.Adj u v
    | .inl u, .inr e => u = parent e
    | .inr e, .inl v => parent e = v
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact T.adj_symm h
    · exact h.symm
    · exact h.symm
    · exact h⟩
  loopless := ⟨by rintro (u | u); exact T.loopless.irrefl u; exact id⟩

namespace leafTree
variable {B E : Type*} (T : SimpleGraph B) (parent : E → B)

def inclusion : T →g leafTree T parent where
  toFun := Sum.inl
  map_rel' := fun h => h

theorem leaf_neighbor (e : E) (x : B ⊕ E)
    (h : (leafTree T parent).Adj (Sum.inr e) x) : x = Sum.inl (parent e) := by
  cases x with
  | inl b => exact congrArg Sum.inl h.symm
  | inr f => exact False.elim h

theorem connected (hT : T.Connected) : (leafTree T parent).Connected := by
  have base : ∀ u v, (leafTree T parent).Reachable (Sum.inl u) (Sum.inl v) :=
    fun u v => (hT u v).map (inclusion T parent)
  let : Nonempty (B ⊕ E) := hT.nonempty.map Sum.inl
  refine ⟨?_⟩
  rintro (u | u) (v | v)
  · exact base u v
  · exact (base u (parent v)).trans (show (leafTree T parent).Adj (Sum.inl (parent v)) (Sum.inr v) from rfl).reachable
  · exact (show (leafTree T parent).Adj (Sum.inr u) (Sum.inl (parent u)) from rfl).reachable.trans (base (parent u) v)
  · exact (show (leafTree T parent).Adj (Sum.inr u) (Sum.inl (parent u)) from rfl).reachable.trans
      ((base (parent u) (parent v)).trans (show (leafTree T parent).Adj (Sum.inl (parent v)) (Sum.inr v) from rfl).reachable)

/-- Adding leaves cannot create a cycle, with no finiteness assumption. -/
theorem acyclic (hT : T.IsAcyclic) : (leafTree T parent).IsAcyclic := by
  classical
  intro x p hp
  have noleaf : ∀ e, Sum.inr e ∉ p.support := by
    intro e he
    let q := p.rotate (Sum.inr e) he
    have hq : q.IsCycle := hp.rotate he
    have h1 := leaf_neighbor T parent e q.snd (q.adj_snd hq.not_nil)
    have h2 := leaf_neighbor T parent e q.penultimate
      ((leafTree T parent).adj_symm (q.adj_penultimate hq.not_nil))
    exact hq.snd_ne_penultimate (h1.trans h2.symm)
  let S : Set (B ⊕ E) := Set.range Sum.inl
  have hs : ∀ v ∈ p.support, v ∈ S := by
    rintro (b | e) hv
    · exact ⟨b,rfl⟩
    · exact False.elim (noleaf e hv)
  let proj : (leafTree T parent).induce S →g T :=
    { toFun := fun v => Classical.choose v.prop
      map_rel' := by
        intro u v h
        change (leafTree T parent).Adj u.val v.val at h
        rw [← Classical.choose_spec u.prop, ← Classical.choose_spec v.prop] at h
        exact h }
  have hinj : Function.Injective proj := by
    intro u v h
    apply Subtype.ext
    rw [← Classical.choose_spec u.prop, ← Classical.choose_spec v.prop]
    exact congrArg Sum.inl h
  have hcycle : (p.induce S hs).IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    simpa using hp
  exact hT ((p.induce S hs).map proj) (hcycle.map hinj)

theorem isTree (hT : T.IsTree) : (leafTree T parent).IsTree :=
  ⟨connected T parent hT.connected, acyclic T parent hT.isAcyclic⟩

end leafTree
end TreewidthHom
