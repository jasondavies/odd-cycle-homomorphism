module
public import TreewidthHom.Enumeration
@[expose] public section
namespace TreewidthHom.Executable
open Enumeration

abbrev SchemaTag := Relational.Tag (Fin 6) Relational.schemaArity

def tagEnumeration : Enumeration SchemaTag :=
  (sum unit (sigma (fin 6) (fun r => sum unit (fin (Relational.schemaArity r))))).map Relational.tagEquiv.symm

theorem tagEnumeration_length : tagEnumeration.elems.length = 18 := by decide

def markers : Markers SchemaTag where
  length c := markerPrimes.get ⟨(tagEnumeration.equiv.symm c).val,by
    have h := (tagEnumeration.equiv.symm c).isLt
    simpa only [markerPrimes_length,tagEnumeration_length] using h⟩
  prime c := markerPrimes_prime _ (List.get_mem _ _)
  injective := by
    intro a b h
    have hh := markerPrimes_nodup.injective_get h
    apply tagEnumeration.equiv.symm.injective
    exact Fin.ext (congrArg Fin.val hh)

theorem markers_bound (c : SchemaTag) : markers.length c ≤ 67 := by
  have h : ∀ p ∈ markerPrimes, p ≤ 67 := by decide
  exact h _ (List.get_mem _ _)

def finFunSucc (α : Type*) (n : ℕ) : (Fin (n+1) → α) ≃ (α × (Fin n → α)) where
  toFun f := (f 0,fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv := by intro f; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by rintro ⟨a,f⟩; rfl

def functions {α : Type*} (a : Enumeration α) : (n : ℕ) → Enumeration (Fin n → α)
  | 0 => ⟨[Fin.elim0],by simp,by intro f; have h : f = Fin.elim0 := funext (fun i => Fin.elim0 i); simp [h]⟩
  | n+1 => (prod a (functions a n)).map (finFunSucc α n).symm

def facts {V : Type} (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) : Enumeration A.Fact :=
  sigma (fin 6) (fun r => (functions vs (Relational.schemaArity r)).subtype (A.holds r))

def incidenceVertices {V : Type} (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) : Enumeration A.Vertex :=
  (sum vs (sigma (facts A vs) (fun f => sum unit (fin (Relational.schemaArity f.1))))).map A.vertexEquiv.symm

def decorated {C : Type} {V : Type} (A : TypedDag C V) (M : Markers C) (vs : Enumeration V) :
    Enumeration (A.Decorated M) :=
  sigma vs (fun v => (fin (M.length (A.color v))).map (ZMod.finEquiv _).toEquiv)

def arcs {V : Type} (D : Digraph V) [DecidableRel D.edge] (vs : Enumeration V) : Enumeration D.Arc :=
  (prod vs vs).subtype (fun p => D.edge p.1 p.2)

def inner : Enumeration Arrow.Inner :=
  (fin 13).subtype (fun i => i ≠ 8 ∧ i ≠ 10)

def assemblyVertices {V : Type} (D : Digraph V) [DecidableRel D.edge] (vs : Enumeration V) :
    Enumeration (Arrow.AssemblyVertex V D.Arc) :=
  sum vs (prod (arcs D vs) inner)

end TreewidthHom.Executable
