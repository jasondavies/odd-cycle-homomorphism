module
public import TreewidthHom.FullReduction
@[expose] public section
namespace TreewidthHom.Executable

/-- An explicit, duplicate-free enumeration; proof fields are erased at runtime. -/
structure Enumeration (α : Type*) where
  elems : List α
  nodup : elems.Nodup
  complete : ∀ x, x ∈ elems

namespace Enumeration
variable {α β : Type*}

def fin (n : ℕ) : Enumeration (Fin n) :=
  ⟨List.finRange n,List.nodup_finRange n,fun _ => List.mem_finRange _⟩

def unit : Enumeration Unit := ⟨[()],by simp,by intro x; cases x; simp⟩
def bool : Enumeration Bool := ⟨[false,true],by decide,by decide⟩

def map (e : Enumeration α) (f : α ≃ β) : Enumeration β where
  elems := e.elems.map f
  nodup := e.nodup.map f.injective
  complete x := List.mem_map.mpr ⟨f.symm x,e.complete _,f.apply_symm_apply x⟩

def sum (a : Enumeration α) (b : Enumeration β) : Enumeration (α ⊕ β) where
  elems := a.elems.map Sum.inl ++ b.elems.map Sum.inr
  nodup := by
    rw [List.nodup_append]
    refine ⟨a.nodup.map Sum.inl_injective,b.nodup.map Sum.inr_injective,?_⟩
    intro x hx y hy he
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    cases he
  complete := by rintro (x|x) <;> simp [a.complete,b.complete]

def sigma {ι : Type*} {δ : ι → Type*} (a : Enumeration ι) (b : ∀ i, Enumeration (δ i)) :
    Enumeration (Σ i, δ i) where
  elems := a.elems.flatMap (fun i => (b i).elems.map (Sigma.mk i))
  nodup := a.nodup.sigma (fun i => (b i).nodup)
  complete := by
    rintro ⟨i,x⟩
    exact List.mem_flatMap.mpr ⟨i,a.complete _,List.mem_map.mpr ⟨x,(b i).complete _,rfl⟩⟩

def prod (a : Enumeration α) (b : Enumeration β) : Enumeration (α × β) :=
  (sigma a (fun _ => b)).map (Equiv.sigmaEquivProd α β)

def subtype (a : Enumeration α) (p : α → Prop) [DecidablePred p] : Enumeration {x // p x} where
  elems := a.elems.filterMap (fun x => if h : p x then some ⟨x,h⟩ else none)
  nodup := by
    apply List.Nodup.filterMap _ a.nodup
    intro x y z hx hy
    split_ifs at hx hy <;> simp_all
    exact congrArg Subtype.val (hx.trans hy.symm)
  complete := by
    intro x
    apply List.mem_filterMap.mpr
    exact ⟨x.val,a.complete _,by simp [x.prop]⟩

def equiv [DecidableEq α] (a : Enumeration α) : Fin a.elems.length ≃ α :=
  a.nodup.getEquivOfForallMemList a.elems a.complete

@[instance_reducible] def toFintype [DecidableEq α] (a : Enumeration α) : Fintype α := ⟨a.elems.toFinset,by simp [a.complete]⟩

end Enumeration
end TreewidthHom.Executable
