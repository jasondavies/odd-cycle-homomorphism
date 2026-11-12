module
public import TreewidthHom.SerializationCost
@[expose] public section
namespace TreewidthHom.Executable
namespace Measured
variable {α β : Type*}

/-- A single primitive operation in the abstract model. -/
def step (a : α) : Measured α := ⟨a,1⟩

def bind (a : Measured α) (f : α → Measured β) : Measured β :=
  let b := f a.value
  ⟨b.value,a.cost+b.cost+1⟩

def mapList (f : α → Measured β) : List α → Measured (List β)
  | [] => ⟨[],1⟩
  | x::xs => let y := f x; let ys := mapList f xs; ⟨y.value::ys.value,y.cost+ys.cost+1⟩

theorem mapList_value (f : α → Measured β) (xs : List α) :
    (mapList f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapList,ih]

theorem mapList_cost (f : α → Measured β) (xs : List α) {c : ℕ}
    (h : ∀ x ∈ xs, (f x).cost ≤ c) : (mapList f xs).cost ≤ (c+1)*xs.length+1 := by
  induction xs with
  | nil => simp [mapList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [mapList,List.length_cons]
    nlinarith

def appendList : List α → List α → Measured (List α)
  | [],ys => ⟨ys,1⟩
  | x::xs,ys => let r := appendList xs ys; ⟨x::r.value,r.cost+1⟩

theorem appendList_spec (xs ys : List α) :
    (appendList xs ys).value = xs++ys ∧ (appendList xs ys).cost = xs.length+1 := by
  induction xs with
  | nil => simp [appendList]
  | cons x xs ih => simp [appendList,ih.1,ih.2]

def flatMapList (f : α → Measured (List β)) : List α → Measured (List β)
  | [] => ⟨[],1⟩
  | x::xs =>
      let y := f x
      let ys := flatMapList f xs
      let z := appendList y.value ys.value
      ⟨z.value,y.cost+ys.cost+z.cost+1⟩

theorem flatMapList_value (f : α → Measured (List β)) (xs : List α) :
    (flatMapList f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flatMapList,appendList_spec,ih]

theorem flatMapList_cost (f : α → Measured (List β)) (xs : List α) {c m : ℕ}
    (hc : ∀ x ∈ xs, (f x).cost ≤ c) (hm : ∀ x ∈ xs, (f x).value.length ≤ m) :
    (flatMapList f xs).cost ≤ (c+m+2)*xs.length+1 := by
  induction xs with
  | nil => simp [flatMapList]
  | cons x xs ih =>
    have hx := hc x (by simp)
    have hy := hm x (by simp)
    have ht := ih (fun y hy => hc y (by simp [hy])) (fun y hy => hm y (by simp [hy]))
    simp only [flatMapList,(appendList_spec _ _).2,List.length_cons]
    nlinarith

def filterMapList (f : α → Measured (Option β)) : List α → Measured (List β)
  | [] => ⟨[],1⟩
  | x::xs =>
      let y := f x
      let ys := filterMapList f xs
      match y.value with
      | none => ⟨ys.value,y.cost+ys.cost+1⟩
      | some z => ⟨z::ys.value,y.cost+ys.cost+2⟩

theorem filterMapList_value (f : α → Measured (Option β)) (xs : List α) :
    (filterMapList f xs).value = xs.filterMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filterMapList,List.filterMap_cons]; split <;> simp_all

theorem filterMapList_cost (f : α → Measured (Option β)) (xs : List α) {c : ℕ}
    (h : ∀ x ∈ xs, (f x).cost ≤ c) : (filterMapList f xs).cost ≤ (c+2)*xs.length+1 := by
  induction xs with
  | nil => simp [filterMapList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [filterMapList,List.length_cons]
    split <;> nlinarith

/-- The constructor adds a zero and shifts the previous indices, so even the
cost of producing the finite range is exposed rather than treated as free. -/
def finRange : (n : ℕ) → Measured (List (Fin n))
  | 0 => ⟨[],1⟩
  | n+1 =>
      let xs := finRange n
      let ys := mapList (fun i => step i.succ) xs.value
      ⟨0::ys.value,xs.cost+ys.cost+1⟩

theorem finRange_value (n : ℕ) : (finRange n).value = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finRange,mapList_value,step,ih,List.finRange_succ]

theorem finRange_cost (n : ℕ) : (finRange n).cost ≤ (n+1)^2 := by
  induction n with
  | zero => simp [finRange]
  | succ n ih =>
    have h := mapList_cost (fun i : Fin n => step i.succ) (finRange n).value
      (c := 1) (by intro i _; exact le_rfl)
    rw [finRange_value,List.length_finRange] at h
    simp only [finRange,finRange_value]
    nlinarith

end Measured
end TreewidthHom.Executable
