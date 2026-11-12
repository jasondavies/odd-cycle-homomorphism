module

public import TreewidthHom.ArrowConfinement

@[expose] public section

/-! # Direction removal preserves homomorphism existence

Replace each arc of a loopless digraph by the ordered-port gadget. The reverse
map uses the general confinement theorem, not a finite bound on the digraph.
-/
namespace TreewidthHom

structure Digraph (V : Type*) where
  edge : V → V → Prop
  loopless : ∀ v, ¬ edge v v

namespace Digraph
variable {V W : Type*}

abbrev Arc (D : Digraph V) := {p : V × V // D.edge p.1 p.2}
abbrev Hom (D : Digraph V) (T : Digraph W) := RelHom D.edge T.edge

def assembly (D : Digraph V) : Arrow.Assembly V D.Arc where
  tail e := e.val.1
  head e := e.val.2
  different e h := D.loopless e.val.1 (h ▸ e.prop)

def NoIsolated (D : Digraph V) : Prop := ∀ v, ∃ w, D.edge v w ∨ D.edge w v

def mapArc {D : Digraph V} {T : Digraph W} (f : Hom D T) (e : D.Arc) : T.Arc :=
  ⟨(f e.val.1, f e.val.2), f.map_rel' e.prop⟩

def mapVertex {D : Digraph V} {T : Digraph W} (f : Hom D T) :
    Arrow.AssemblyVertex V D.Arc → Arrow.AssemblyVertex W T.Arc
  | .inl v => .inl (f v)
  | .inr (e,u) => .inr (mapArc f e,u)

theorem mapVertex_embed {D : Digraph V} {T : Digraph W} (f : Hom D T)
    (e : D.Arc) (v : Fin 13) :
    mapVertex f (D.assembly.embed e v) = T.assembly.embed (mapArc f e) v := by
  by_cases h : v = 8 <;> by_cases h' : v = 10 <;>
    simp_all [Arrow.Assembly.embed, mapVertex, assembly, mapArc]

/-- A directed homomorphism extends coordinatewise over every gadget. -/
def liftHom {D : Digraph V} {T : Digraph W} (f : Hom D T) :
    D.assembly.graph →g T.assembly.graph where
  toFun := mapVertex f
  map_rel' := by
    rintro x y ⟨e,u,v,h,rfl,rfl⟩
    rw [mapVertex_embed, mapVertex_embed]
    exact T.assembly.embed_adj (mapArc f e) h

/-- Recover a directed homomorphism from an undirected one. Only the source
needs to have no isolated vertices. -/
theorem recoverHom {D : Digraph V} {T : Digraph W} (hD : D.NoIsolated)
    (f : D.assembly.graph →g T.assembly.graph) : Nonempty (Hom D T) := by
  classical
  have copies : ∀ e : D.Arc, ∃ c : T.Arc, ∀ v,
      f (D.assembly.embed e v) = T.assembly.embed c v := by
    intro e
    let fe : Arrow.graph →g T.assembly.graph :=
      { toFun := fun v => f (D.assembly.embed e v)
        map_rel' := fun h => f.map_adj (D.assembly.embed_adj e h) }
    exact T.assembly.confinement fe
  choose c hc using copies
  have bases : ∀ v, ∃ w, f (Sum.inl v) = Sum.inl w := by
    intro v
    obtain ⟨w,h | h⟩ := hD v
    · let e : D.Arc := ⟨(v,w),h⟩
      exact ⟨(c e).val.1, by simpa [assembly, e] using hc e 8⟩
    · let e : D.Arc := ⟨(w,v),h⟩
      exact ⟨(c e).val.2, by simpa [assembly, e] using hc e 10⟩
  choose g hg using bases
  refine ⟨⟨g, ?_⟩⟩
  intro u v h
  let e : D.Arc := ⟨(u,v),h⟩
  have hu : f (Sum.inl u) = Sum.inl (c e).val.1 := by
    simpa [assembly, e] using hc e 8
  have hv : f (Sum.inl v) = Sum.inl (c e).val.2 := by
    simpa [assembly, e] using hc e 10
  have hgu : g u = (c e).val.1 := Sum.inl.inj ((hg u).symm.trans hu)
  have hgv : g v = (c e).val.2 := Sum.inl.inj ((hg v).symm.trans hv)
  rw [hgu,hgv]
  exact (c e).prop

/-- The final, unlabelled graph encoding preserves the decision problem. -/
theorem directionReduction_iff {D : Digraph V} {T : Digraph W} (hD : D.NoIsolated) :
    Nonempty (D.assembly.graph →g T.assembly.graph) ↔ Nonempty (Hom D T) := by
  constructor
  · rintro ⟨f⟩; exact recoverHom hD f
  · rintro ⟨f⟩; exact ⟨liftHom f⟩

/-- Exact vertex cost: one base vertex per original vertex and eleven per arc. -/
theorem directionReduction_card (D : Digraph V) [Fintype V] [Fintype D.Arc] :
    Fintype.card (Arrow.AssemblyVertex V D.Arc) = Fintype.card V + 11 * Fintype.card D.Arc := by
  have hc : Fintype.card Arrow.Inner = 11 := by decide
  simp [Arrow.AssemblyVertex, Fintype.card_sum, Fintype.card_prod, hc, Nat.mul_comm]

end Digraph
end TreewidthHom
