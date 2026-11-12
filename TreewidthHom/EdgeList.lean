module
public import TreewidthHom.ExecutableRelations
@[expose] public section
namespace TreewidthHom.Executable
open SimpleGraph

/-- An explicit finite graph encoding with integer vertex identifiers. -/
structure EdgeList where
  order : ℕ
  edges : List (Fin order × Fin order)
  loopless : ∀ e ∈ edges, e.1 ≠ e.2

def EdgeList.graph (g : EdgeList) : SimpleGraph (Fin g.order) where
  Adj u v := (u,v) ∈ g.edges ∨ (v,u) ∈ g.edges
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro v h; exact g.loopless (v,v) (h.elim id id) rfl⟩

instance (g : EdgeList) : DecidableRel g.graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def EdgeList.data (g : EdgeList) : ℕ × List (ℕ × ℕ) :=
  (g.order,g.edges.map (fun e => (e.1.val,e.2.val)))

/-- A vertex enumeration and a sparse adjacency certificate for a specified graph. -/
structure Presentation {V : Type} (G : SimpleGraph V) where
  vertices : Enumeration V
  edges : List (V × V)
  correct : ∀ u v, G.Adj u v ↔ (u,v) ∈ edges ∨ (v,u) ∈ edges

namespace Presentation
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

def encode (p : Presentation G) : EdgeList where
  order := p.vertices.elems.length
  edges := p.edges.map (fun e => (p.vertices.equiv.symm e.1,p.vertices.equiv.symm e.2))
  loopless := by
    intro e he h
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := List.mem_map.mp he
    exact G.ne_of_adj ((p.correct u v).mpr (Or.inl huv)) (p.vertices.equiv.symm.injective h)

theorem encode_adj (p : Presentation G) (u v : Fin p.encode.order) :
    p.encode.graph.Adj u v ↔ G.Adj (p.vertices.equiv u) (p.vertices.equiv v) := by
  rw [p.correct]
  change ((_ ∈ p.edges.map _) ∨ (_ ∈ p.edges.map _)) ↔ _
  have h : ∀ a b : Fin p.vertices.elems.length,
      (a,b) ∈ p.edges.map (fun e => (p.vertices.equiv.symm e.1,p.vertices.equiv.symm e.2)) ↔
      (p.vertices.equiv a,p.vertices.equiv b) ∈ p.edges := by
    intro a b
    constructor
    · rintro h
      obtain ⟨⟨x,y⟩,hxy,he⟩ := List.mem_map.mp h
      have h1 := congrArg (fun e => p.vertices.equiv e.1) he
      have h2 := congrArg (fun e => p.vertices.equiv e.2) he
      simp only [Equiv.apply_symm_apply] at h1 h2
      simpa [← h1,← h2] using hxy
    · intro hab
      exact List.mem_map.mpr ⟨_,hab,by simp⟩
  exact or_congr (h u v) (h v u)

def iso (p : Presentation G) : p.encode.graph ≃g G where
  toEquiv := p.vertices.equiv
  map_rel_iff' := fun {u v} => (p.encode_adj u v).symm

end Presentation

def gadgetEdges : List (Fin 13 × Fin 13) :=
  ((Enumeration.fin 13).prod (Enumeration.fin 13)).elems.filter (fun p => decide (Arrow.graph.Adj p.1 p.2))

@[simp] theorem mem_gadgetEdges (u v : Fin 13) : (u,v) ∈ gadgetEdges ↔ Arrow.graph.Adj u v := by
  simp [gadgetEdges,Enumeration.complete]

def assemblyPresentation {V E : Type} (A : Arrow.Assembly V E)
    (vs : Enumeration V) (es : Enumeration E) : Presentation A.graph where
  vertices := vs.sum (es.prod inner)
  edges := es.elems.flatMap (fun e => gadgetEdges.map (fun p => (A.embed e p.1,A.embed e p.2)))
  correct := by
    intro x y
    have hh : ∀ x y, (x,y) ∈ es.elems.flatMap (fun e => gadgetEdges.map (fun p => (A.embed e p.1,A.embed e p.2))) ↔
        A.graph.Adj x y := by
      intro x y
      constructor
      · intro h
        obtain ⟨e,_,h⟩ := List.mem_flatMap.mp h
        obtain ⟨⟨u,v⟩,huv,he⟩ := List.mem_map.mp h
        exact ⟨e,u,v,(mem_gadgetEdges u v).mp huv,congrArg Prod.fst he,congrArg Prod.snd he⟩
      · rintro ⟨e,u,v,h,rfl,rfl⟩
        exact List.mem_flatMap.mpr ⟨e,es.complete _,List.mem_map.mpr ⟨(u,v),(mem_gadgetEdges u v).mpr h,rfl⟩⟩
    rw [hh,hh]
    exact ⟨Or.inl,fun h => h.elim id A.graph.adj_symm⟩

end TreewidthHom.Executable

namespace TreewidthHom
open SimpleGraph

theorem HasWidth.of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    {w : ℕ} (h : HasWidth G w) (e : G ≃g H) : HasWidth H w := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := h
  let := d
  let D' := D.mapEquiv e.toEquiv (fun _ _ h => e.map_rel_iff.mp h)
  refine ⟨inferInstance,B,T,D',?_⟩
  intro b
  rw [Decomposition.mapEquiv_card]
  exact hw b

theorem hom_iff_of_iso {V W X Y : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    {G' : SimpleGraph X} {H' : SimpleGraph Y} (e : G ≃g G') (f : H ≃g H') :
    Nonempty (G →g H) ↔ Nonempty (G' →g H') := by
  constructor
  · rintro ⟨h⟩; exact ⟨f.toHom.comp (h.comp e.symm.toHom)⟩
  · rintro ⟨h⟩; exact ⟨f.symm.toHom.comp (h.comp e.toHom)⟩
end TreewidthHom
