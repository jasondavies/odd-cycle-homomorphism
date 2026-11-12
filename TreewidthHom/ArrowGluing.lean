module

public import TreewidthHom.ArrowSearch

@[expose] public section

/-! # Arbitrary assemblies of ordered-port gadgets

A copy has two distinct endpoints in an arbitrary vertex type. Private vertices
are indexed by the copy. There is no finiteness assumption on the assembly.
-/
namespace TreewidthHom.Arrow

abbrev Inner := {v : Fin 13 // v ≠ 8 ∧ v ≠ 10}
abbrev AssemblyVertex (V E : Type*) := V ⊕ (E × Inner)

structure Assembly (V E : Type*) where
  tail : E → V
  head : E → V
  different : ∀ e, tail e ≠ head e

namespace Assembly
variable {V E : Type*} (A : Assembly V E)

/-- The inclusion of a gadget copy; its two ordered ports are glued to endpoints. -/
def embed (e : E) (v : Fin 13) : AssemblyVertex V E :=
  if h : v = 8 then Sum.inl (A.tail e)
  else if h' : v = 10 then Sum.inl (A.head e)
  else Sum.inr (e, ⟨v,h,h'⟩)

@[simp] theorem embed_tail (e : E) : A.embed e 8 = Sum.inl (A.tail e) := by simp [embed]
@[simp] theorem embed_head (e : E) : A.embed e 10 = Sum.inl (A.head e) := by simp [embed]
@[simp] theorem embed_inner (e : E) (v : Inner) :
    A.embed e v.val = Sum.inr (e,v) := by simp [embed, v.prop.1, v.prop.2]

theorem embed_injective (e : E) : Function.Injective (A.embed e) := by
  intro u v h
  have hd := A.different e
  by_cases hu : u = 8 <;> by_cases hu' : u = 10 <;>
    by_cases hv : v = 8 <;> by_cases hv' : v = 10 <;> simp_all [embed]

/-- A private vertex determines both its copy and its coordinate. -/
theorem embed_eq_inner_iff (e f : E) (v : Fin 13) (w : Inner) :
    A.embed e v = Sum.inr (f,w) ↔ e = f ∧ v = w.val := by
  have hw := w.prop
  by_cases h : v = 8 <;> by_cases h' : v = 10 <;> simp_all [embed, ne_comm, Subtype.ext_iff]

/-- No gadget edge joins two ports. -/
theorem edge_has_inner : ∀ u v : Fin 13, graph.Adj u v →
    (u ≠ 8 ∧ u ≠ 10) ∨ (v ≠ 8 ∧ v ≠ 10) := by decide

def Adjacent (x y : AssemblyVertex V E) : Prop :=
  ∃ e u v, graph.Adj u v ∧ A.embed e u = x ∧ A.embed e v = y

def graph : SimpleGraph (AssemblyVertex V E) where
  Adj := A.Adjacent
  symm := ⟨by
    rintro x y ⟨e,u,v,h,hu,hv⟩
    exact ⟨e,v,u,Arrow.adj_symm u v h,hv,hu⟩⟩
  loopless := ⟨by
    rintro x ⟨e,u,v,h,hu,hv⟩
    have he := A.embed_injective e (hu.trans hv.symm)
    exact Arrow.graph.ne_of_adj h he⟩

theorem embed_adj (e : E) {u v : Fin 13} (h : Arrow.graph.Adj u v) :
    A.graph.Adj (A.embed e u) (A.embed e v) := ⟨e,u,v,h,rfl,rfl⟩

theorem private_adj_same_copy {e f : E} {u v : Inner}
    (h : A.graph.Adj (Sum.inr (e,u)) (Sum.inr (f,v))) : e = f := by
  obtain ⟨c,x,y,_,hx,hy⟩ := h
  have h1 := (A.embed_eq_inner_iff c e x u).mp hx
  have h2 := (A.embed_eq_inner_iff c f y v).mp hy
  exact h1.1.symm.trans h2.1

/-- Every neighbor of a private vertex belongs to the same gadget copy. -/
theorem neighbor_of_private {e : E} {u : Inner} {y : AssemblyVertex V E}
    (h : A.graph.Adj (Sum.inr (e,u)) y) : ∃ v, A.embed e v = y := by
  obtain ⟨c,x,v,_,hx,hy⟩ := h
  have hc := ((A.embed_eq_inner_iff c e x u).mp hx).1
  subst c
  exact ⟨v,hy⟩

/-- Edges in the assembly whose endpoints belong to one copy are its own edges. -/
theorem embed_adj_iff (e : E) (u v : Fin 13) :
    A.graph.Adj (A.embed e u) (A.embed e v) ↔ Arrow.graph.Adj u v := by
  constructor
  · rintro ⟨c,x,y,h,hx,hy⟩
    rcases edge_has_inner x y h with hx' | hy'
    · have he : c = e := by
        have hp : A.embed e u = Sum.inr (c,⟨x,hx'⟩) := hx.symm.trans (A.embed_inner c ⟨x,hx'⟩)
        exact ((A.embed_eq_inner_iff e c u ⟨x,hx'⟩).mp hp).1.symm
      subst c
      have hxu := A.embed_injective e hx
      have hyv := A.embed_injective e hy
      simpa [hxu, hyv] using h
    · have he : c = e := by
        have hp : A.embed e v = Sum.inr (c,⟨y,hy'⟩) := hy.symm.trans (A.embed_inner c ⟨y,hy'⟩)
        exact ((A.embed_eq_inner_iff e c v ⟨y,hy'⟩).mp hp).1.symm
      subst c
      have hxu := A.embed_injective e hx
      have hyv := A.embed_injective e hy
      simpa [hxu, hyv] using h
  · exact A.embed_adj e

end Assembly
end TreewidthHom.Arrow
