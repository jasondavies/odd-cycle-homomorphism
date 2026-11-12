module
public import TreewidthHom.MeasuredEnumeration
@[expose] public section
namespace TreewidthHom.Executable
open Enumeration
variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (A : Arrow.Assembly V E) (vs : Enumeration V) (es : Enumeration E)

/-- Instrumented list lookup, including the recursion through every skipped cell. -/
def getMeasured {α : Type*} : (xs : List α) → Fin xs.length → Measured α
  | [],i => Fin.elim0 i
  | x::xs,i => if h : i.val = 0 then ⟨x,1⟩ else
      let r := getMeasured xs ⟨i.val-1,by have := i.isLt; simp only [List.length_cons] at this; omega⟩
      ⟨r.value,r.cost+1⟩

theorem getMeasured_value {α : Type*} (xs : List α) (i : Fin xs.length) :
    (getMeasured xs i).value = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [getMeasured]
    · simp [getMeasured,ih]

theorem getMeasured_cost {α : Type*} (xs : List α) (i : Fin xs.length) :
    (getMeasured xs i).cost ≤ xs.length := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [getMeasured]
    · simp only [getMeasured,Fin.val_succ,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceDIte,Nat.add_sub_cancel,List.length_cons]
      exact Nat.add_le_add_right (ih j) 1

/-- Equality costs for base vertices are parameterized; fixed gadget-coordinate
operations are charged unit cost. Numeric arithmetic here has unit cost too. -/
def portMeasured (eqCost : ℕ) (i : ℕ) (e : E) (u : Fin 13) : Measured ℕ :=
  if h : u = 8 then
    let r := indexMeasured eqCost (A.tail e) vs.elems
    ⟨r.value,r.cost+2⟩
  else if h' : u = 10 then
    let r := indexMeasured eqCost (A.head e) vs.elems
    ⟨r.value,r.cost+3⟩
  else
    let r := indexMeasured 1 (⟨u,h,h'⟩ : Arrow.Inner) inner.elems
    let n := lengthMeasured vs.elems
    ⟨n.value+(r.value+inner.elems.length*i),r.cost+n.cost+7⟩

set_option backward.isDefEq.respectTransparency false in
theorem portMeasured_value (eqCost : ℕ) (i : Fin es.elems.length) (u : Fin 13) :
    (portMeasured A vs eqCost i.val (es.equiv i) u).value = (numberedPort A vs es i u).val := by
  by_cases h : u = 8 <;> by_cases h' : u = 10 <;>
    simp [portMeasured,numberedPort,h,h',indexMeasured_value,lengthMeasured_spec,Enumeration.equiv,
      List.Nodup.getEquivOfForallMemList,finSumFinEquiv,finProdFinEquiv]

omit [DecidableEq E] in
theorem portMeasured_cost (eqCost : ℕ) (i : ℕ) (e : E) (u : Fin 13) :
    (portMeasured A vs eqCost i e u).cost ≤ (eqCost+2)*vs.elems.length+50 := by
  have ha := indexMeasured_cost eqCost (A.tail e) vs.elems
  have hb := indexMeasured_cost eqCost (A.head e) vs.elems
  have hi : ∀ z : Arrow.Inner, (indexMeasured 1 z inner.elems).cost ≤ 34 := by
    intro z
    exact indexMeasured_cost 1 z inner.elems
  unfold portMeasured
  split_ifs with h h'
  · dsimp; omega
  · dsimp; omega
  · have hh := hi ⟨u,h,h'⟩
    dsimp only
    rw [(lengthMeasured_spec _).2]
    nlinarith [Nat.zero_le (eqCost*vs.elems.length)]

def copyMeasured (eqCost : ℕ) (i : Fin es.elems.length) : Measured (List (ℕ × ℕ)) :=
  let e := getMeasured es.elems i
  let out := Measured.mapList (fun uv =>
    let a := portMeasured A vs eqCost i.val e.value uv.1
    let b := portMeasured A vs eqCost i.val e.value uv.2
    ⟨(a.value,b.value),a.cost+b.cost+1⟩) gadgetEdges
  ⟨out.value,e.cost+out.cost+1⟩

theorem copyMeasured_value (eqCost : ℕ) (i : Fin es.elems.length) :
    (copyMeasured A vs es eqCost i).value = gadgetEdges.map
      (fun p => ((numberedPort A vs es i p.1).val,(numberedPort A vs es i p.2).val)) := by
  simp only [copyMeasured,Measured.mapList_value,getMeasured_value]
  apply List.map_congr_left
  intro p _
  exact Prod.ext (portMeasured_value A vs es eqCost i p.1) (portMeasured_value A vs es eqCost i p.2)

theorem gadgetEdges_length : gadgetEdges.length = 30 := by decide

omit [DecidableEq E] in
theorem copyMeasured_cost (eqCost : ℕ) (i : Fin es.elems.length) :
    (copyMeasured A vs es eqCost i).cost ≤ es.elems.length+60*(eqCost+2)*vs.elems.length+3062 := by
  have hg := getMeasured_cost es.elems i
  have h := Measured.mapList_cost (fun uv : Fin 13 × Fin 13 =>
    let a := portMeasured A vs eqCost i.val (getMeasured es.elems i).value uv.1
    let b := portMeasured A vs eqCost i.val (getMeasured es.elems i).value uv.2
    (⟨(a.value,b.value),a.cost+b.cost+1⟩ : Measured (ℕ × ℕ))) gadgetEdges
    (c := 2*((eqCost+2)*vs.elems.length+50)+1) (by
      intro uv _
      have h1 := portMeasured_cost A vs eqCost i.val (getMeasured es.elems i).value uv.1
      have h2 := portMeasured_cost A vs eqCost i.val (getMeasured es.elems i).value uv.2
      dsimp
      omega)
  rw [gadgetEdges_length] at h
  dsimp only [copyMeasured]
  nlinarith

/-- Executes the sparse direction-gadget serialization from supplied vertex and
arc lists. Enumeration and relation-testing costs are not included in this stage. -/
def indexedAssemblyMeasured (eqCost : ℕ) : Measured (ℕ × List (ℕ × ℕ)) :=
  let n := lengthMeasured vs.elems
  let m := lengthMeasured es.elems
  let indices := Measured.finRange es.elems.length
  let out := Measured.flatMapList (copyMeasured A vs es eqCost) indices.value
  ⟨(n.value+m.value*11,out.value),n.cost+2*m.cost+indices.cost+out.cost+3⟩

theorem indexedAssemblyMeasured_value (eqCost : ℕ) :
    (indexedAssemblyMeasured A vs es eqCost).value = (indexedAssembly A vs es).data := by
  simp only [indexedAssemblyMeasured,lengthMeasured_spec,Measured.flatMapList_value,
    Measured.finRange_value,copyMeasured_value,EdgeList.data,indexedAssembly,numberedEdges,List.map_flatMap,List.map_map]
  rfl

theorem indexedAssemblyMeasured_cost (eqCost : ℕ) :
    (indexedAssemblyMeasured A vs es eqCost).cost ≤
      (es.elems.length+60*(eqCost+2)*vs.elems.length+3094)*es.elems.length+
      (es.elems.length+1)^2+vs.elems.length+2*es.elems.length+7 := by
  have h1 := Measured.finRange_cost es.elems.length
  have h2 := Measured.flatMapList_cost (copyMeasured A vs es eqCost)
    (Measured.finRange es.elems.length).value
    (c := es.elems.length+60*(eqCost+2)*vs.elems.length+3062) (m := 30)
    (by intro i _; exact copyMeasured_cost A vs es eqCost i)
    (by intro i _; rw [copyMeasured_value,List.length_map,gadgetEdges_length])
  rw [Measured.finRange_value,List.length_finRange] at h2
  simp only [indexedAssemblyMeasured,(lengthMeasured_spec _).2,Measured.finRange_value]
  nlinarith

/-- A polynomial comparison-model bound for the actual measured serialization. -/
theorem indexedAssemblyMeasured_quadratic (eqCost b : ℕ)
    (hv : vs.elems.length ≤ b) (he : es.elems.length ≤ b) :
    (indexedAssemblyMeasured A vs es eqCost).cost ≤ 10000*(eqCost+2)*(b+1)^2 := by
  have hc := indexedAssemblyMeasured_cost A vs es eqCost
  have hp := Nat.mul_le_mul_left (60*(eqCost+2)) hv
  have hm := Nat.mul_le_mul (show es.elems.length+60*(eqCost+2)*vs.elems.length+3094 ≤
      b+60*(eqCost+2)*b+3094 by omega) he
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right he 1) 2
  have hpos : 0 ≤ eqCost*b^2 := Nat.zero_le _
  have hpos' : 0 ≤ eqCost*b := Nat.zero_le _
  nlinarith

/-- The supplied lists' preparation remains outside this stage theorem. -/
theorem indexedAssemblyMeasured_order_bound (eqCost : ℕ) :
    (indexedAssemblyMeasured A vs es eqCost).cost ≤
      10000*(eqCost+2)*((indexedAssembly A vs es).order+1)^2 := by
  apply indexedAssemblyMeasured_quadratic
  · change vs.elems.length ≤ vs.elems.length+es.elems.length*inner.elems.length
    omega
  · change es.elems.length ≤ vs.elems.length+es.elems.length*11
    omega

end TreewidthHom.Executable
