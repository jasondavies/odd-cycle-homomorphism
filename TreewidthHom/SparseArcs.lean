module
public import TreewidthHom.ExecutableRelations
@[expose] public section
namespace TreewidthHom.Executable
open Enumeration
set_option synthInstance.maxSize 1000
variable {V : Type}
variable (A : Relational (Fin 6) Relational.schemaArity V)

abbrev PortCode := Σ f : A.Fact, Fin (Relational.schemaArity f.1)
abbrev ArcCode := A.typedDag.Decorated markers ⊕ (Bool × PortCode A)

def arcOfCode : ArcCode A → (A.typedDag.encoded markers).Arc
  | .inl ⟨v,z⟩ => ⟨(⟨v,z⟩,⟨v,z+1⟩),.cycle v z⟩
  | .inr (false,⟨f,i⟩) => ⟨(⟨.tuple f,0⟩,⟨.port f i,0⟩),.base (.first f i)⟩
  | .inr (true,⟨f,i⟩) => ⟨(⟨.port f i,0⟩,⟨.domain (f.2.val i),0⟩),.base (.second f i)⟩

theorem arcOfCode_injective : Function.Injective (arcOfCode A) := by
  intro a b h
  have hs := congrArg (fun e : (A.typedDag.encoded markers).Arc => e.val.1) h
  have ht := congrArg (fun e : (A.typedDag.encoded markers).Arc => e.val.2) h
  have hs' := congrArg Sigma.fst hs
  have ht' := congrArg Sigma.fst ht
  rcases a with ⟨v,z⟩ | ⟨ab,⟨f,i⟩⟩ <;> rcases b with ⟨w,t⟩ | ⟨bb,⟨g,j⟩⟩
  · exact congrArg Sum.inl hs
  · cases bb <;> dsimp [arcOfCode] at hs' ht'
    · have he := hs'.symm.trans ht'; cases he
    · have he := hs'.symm.trans ht'; cases he
  · cases ab <;> dsimp [arcOfCode] at hs' ht'
    · have he := hs'.trans ht'.symm; cases he
    · have he := hs'.trans ht'.symm; cases he
  · cases ab <;> cases bb <;> dsimp [arcOfCode] at hs' ht'
    · have hf := Relational.Vertex.tuple.inj hs'
      subst g
      have hi : i = j := by cases ht'; rfl
      subst j
      rfl
    · cases hs'
    · cases hs'
    · have he : (⟨f,i⟩ : PortCode A) = ⟨g,j⟩ := by cases hs'; rfl
      exact congrArg (fun p : PortCode A => (Sum.inr (true,p) : ArcCode A)) he

theorem arcOfCode_surjective : Function.Surjective (arcOfCode A) := by
  rintro ⟨⟨x,y⟩,h⟩
  cases h with
  | cycle v z => exact ⟨.inl ⟨v,z⟩,rfl⟩
  | base h =>
    cases h with
    | first f i => exact ⟨.inr (false,⟨f,i⟩),rfl⟩
    | second f i => exact ⟨.inr (true,⟨f,i⟩),rfl⟩

def sparseArcs [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) :
    Enumeration (A.typedDag.encoded markers).Arc where
  elems := ((decorated A.typedDag markers (incidenceVertices A vs)).sum
    (bool.prod (sigma (facts A vs) (fun f => fin (Relational.schemaArity f.1))))).elems.map (arcOfCode A)
  nodup := Enumeration.nodup _ |>.map (arcOfCode_injective A)
  complete := by
    intro e
    obtain ⟨c,rfl⟩ := arcOfCode_surjective A e
    exact List.mem_map.mpr ⟨c,Enumeration.complete _ c,rfl⟩

end TreewidthHom.Executable
