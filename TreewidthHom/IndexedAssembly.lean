module
public import TreewidthHom.EdgeList
@[expose] public section
namespace TreewidthHom.Executable
open Enumeration
variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (A : Arrow.Assembly V E) (vs : Enumeration V) (es : Enumeration E)

def assemblyOrder := vs.elems.length + es.elems.length * inner.elems.length

def assemblyNumbering : Fin (assemblyOrder vs es) ≃ Arrow.AssemblyVertex V E :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr vs.equiv
    (finProdFinEquiv.symm.trans (Equiv.prodCongr es.equiv inner.equiv)))

/-- Each private vertex is numbered arithmetically using its copy's known index.
Only the two glued ports need a search in the base-vertex list. -/
def numberedPort (i : Fin es.elems.length) (u : Fin 13) : Fin (assemblyOrder vs es) :=
  if h : u = 8 then finSumFinEquiv (.inl (vs.equiv.symm (A.tail (es.equiv i))))
  else if h' : u = 10 then finSumFinEquiv (.inl (vs.equiv.symm (A.head (es.equiv i))))
  else finSumFinEquiv (.inr (finProdFinEquiv (i,inner.equiv.symm ⟨u,h,h'⟩)))

set_option backward.isDefEq.respectTransparency false in
theorem numbering_port (i : Fin es.elems.length) (u : Fin 13) :
    assemblyNumbering vs es (numberedPort A vs es i u) = A.embed (es.equiv i) u := by
  by_cases h : u = 8 <;> by_cases h' : u = 10 <;>
    simp [numberedPort,assemblyNumbering,Arrow.Assembly.embed,finSumFinEquiv,h,h']

def numberedEdges : List (Fin (assemblyOrder vs es) × Fin (assemblyOrder vs es)) :=
  (List.finRange es.elems.length).flatMap (fun i =>
    gadgetEdges.map (fun p => (numberedPort A vs es i p.1,numberedPort A vs es i p.2)))

def indexedAssembly : EdgeList where
  order := assemblyOrder vs es
  edges := numberedEdges A vs es
  loopless := by
    intro e he hh
    obtain ⟨i,_,he⟩ := List.mem_flatMap.mp he
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := List.mem_map.mp he
    have h := congrArg (assemblyNumbering vs es) hh
    rw [numbering_port,numbering_port] at h
    exact Arrow.graph.ne_of_adj ((mem_gadgetEdges u v).mp huv) (A.embed_injective _ h)

theorem numbered_mem_adj (a b : Fin (assemblyOrder vs es)) :
    (a,b) ∈ numberedEdges A vs es ↔
      A.graph.Adj (assemblyNumbering vs es a) (assemblyNumbering vs es b) := by
  constructor
  · intro h
    obtain ⟨i,_,h⟩ := List.mem_flatMap.mp h
    obtain ⟨⟨u,v⟩,huv,he⟩ := List.mem_map.mp h
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    rw [← h1,← h2,numbering_port,numbering_port]
    exact A.embed_adj _ ((mem_gadgetEdges u v).mp huv)
  · rintro ⟨e,u,v,huv,hu,hv⟩
    let i := es.equiv.symm e
    have h1 : numberedPort A vs es i u = a := by
      apply (assemblyNumbering vs es).injective
      simpa [numbering_port,i] using hu
    have h2 : numberedPort A vs es i v = b := by
      apply (assemblyNumbering vs es).injective
      simpa [numbering_port,i] using hv
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨(u,v),(mem_gadgetEdges u v).mpr huv,Prod.ext h1 h2⟩⟩

def indexedAssemblyIso : (indexedAssembly A vs es).graph ≃g A.graph where
  toEquiv := assemblyNumbering vs es
  map_rel_iff' := by
    intro a b
    change A.graph.Adj _ _ ↔ ((_ ∈ numberedEdges A vs es) ∨ (_ ∈ numberedEdges A vs es))
    exact ⟨fun h => Or.inl ((numbered_mem_adj A vs es a b).mpr h),
      fun h => h.elim ((numbered_mem_adj A vs es a b).mp)
        (fun h => A.graph.adj_symm ((numbered_mem_adj A vs es b a).mp h))⟩

end TreewidthHom.Executable
