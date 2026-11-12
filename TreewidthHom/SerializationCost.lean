module
public import TreewidthHom.ExecutableReduction
@[expose] public section
namespace TreewidthHom.Executable

/-- A result and its cost in the list-traversal/comparison model below.
This is not a Turing-machine or bit-cost claim. -/
structure Measured (α : Type*) where
  value : α
  cost : ℕ

/-- One step per visited list cell, plus one equality comparison per nonempty cell.
All calls to the supplied equality operation are charged; its internal bit cost
is deliberately left as a separate model parameter. -/
def indexMeasured {α : Type*} [DecidableEq α] (eqCost : ℕ) (x : α) : List α → Measured ℕ
  | [] => ⟨0,1⟩
  | y::ys => if x = y then ⟨0,eqCost+1⟩ else
      let r := indexMeasured eqCost x ys
      ⟨r.value+1,r.cost+eqCost+2⟩

theorem indexMeasured_value {α : Type*} [DecidableEq α] (eqCost : ℕ) (x : α) (xs : List α) :
    (indexMeasured eqCost x xs).value = xs.idxOf x := by
  induction xs with
  | nil => simp [indexMeasured]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [indexMeasured,h]
    · simp [indexMeasured,h,Ne.symm h,ih]

theorem indexMeasured_cost {α : Type*} [DecidableEq α] (eqCost : ℕ) (x : α) (xs : List α) :
    (indexMeasured eqCost x xs).cost ≤ (eqCost+2)*xs.length+1 := by
  induction xs with
  | nil => simp [indexMeasured]
  | cons y ys ih =>
    by_cases h : x = y
    · simp only [indexMeasured,h,↓reduceIte,List.length_cons]
      nlinarith
    · simp only [indexMeasured,h,↓reduceIte,List.length_cons]
      nlinarith

/-- Serializes the endpoints by executing the same linear searches used by the
bijection in `Presentation.encode`. Three steps pay for the output pair/list cell. -/
def endpointsMeasured {α : Type*} [DecidableEq α] (eqCost : ℕ) (vs : List α) :
    List (α × α) → Measured (List (ℕ × ℕ))
  | [] => ⟨[],1⟩
  | (u,v)::es =>
      let a := indexMeasured eqCost u vs
      let b := indexMeasured eqCost v vs
      let r := endpointsMeasured eqCost vs es
      ⟨(a.value,b.value)::r.value,a.cost+b.cost+r.cost+3⟩

theorem endpointsMeasured_value {α : Type*} [DecidableEq α] (eqCost : ℕ)
    (vs : List α) (es : List (α × α)) :
    (endpointsMeasured eqCost vs es).value = es.map (fun e => (vs.idxOf e.1,vs.idxOf e.2)) := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e; simp [endpointsMeasured,indexMeasured_value,ih]

theorem endpointsMeasured_cost {α : Type*} [DecidableEq α] (eqCost : ℕ)
    (vs : List α) (es : List (α × α)) :
    (endpointsMeasured eqCost vs es).cost ≤ (2*(eqCost+2)*vs.length+5)*es.length+1 := by
  induction es with
  | nil => simp [endpointsMeasured]
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    have ha := indexMeasured_cost eqCost u vs
    have hb := indexMeasured_cost eqCost v vs
    simp only [endpointsMeasured,List.length_cons]
    nlinarith

def lengthMeasured {α : Type*} : List α → Measured ℕ
  | [] => ⟨0,1⟩
  | _::xs => let r := lengthMeasured xs; ⟨r.value+1,r.cost+1⟩

theorem lengthMeasured_spec {α : Type*} (xs : List α) :
    (lengthMeasured xs).value = xs.length ∧ (lengthMeasured xs).cost = xs.length+1 := by
  induction xs with
  | nil => simp [lengthMeasured]
  | cons x xs ih => simp [lengthMeasured,ih.1,ih.2]

/-- Actual executable serialization, including the vertex-list length traversal. -/
def serializeMeasured {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (eqCost : ℕ) (p : Presentation G) : Measured (ℕ × List (ℕ × ℕ)) :=
  let n := lengthMeasured p.vertices.elems
  let e := endpointsMeasured eqCost p.vertices.elems p.edges
  ⟨(n.value,e.value),n.cost+e.cost+1⟩

theorem serializeMeasured_value {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (eqCost : ℕ) (p : Presentation G) :
    (serializeMeasured eqCost p).value = p.encode.data := by
  simp only [serializeMeasured,lengthMeasured_spec,endpointsMeasured_value,
    EdgeList.data,Presentation.encode,List.map_map]
  rfl

theorem serializeMeasured_cost {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (eqCost : ℕ) (p : Presentation G) :
    (serializeMeasured eqCost p).cost ≤
      (2*(eqCost+2)*p.vertices.elems.length+5)*p.edges.length+p.vertices.elems.length+3 := by
  have h := endpointsMeasured_cost eqCost p.vertices.elems p.edges
  dsimp only [serializeMeasured]
  rw [(lengthMeasured_spec _).2]
  omega

end TreewidthHom.Executable
