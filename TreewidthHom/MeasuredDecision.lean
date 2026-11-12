module
public import TreewidthHom.EnumerationBounds
@[expose] public section
namespace TreewidthHom.Executable
namespace Decision

/-- A comparison primitive with its explicitly supplied cost. -/
def atom (p : Prop) [Decidable p] (cost : ℕ) : Measured (Decidable p) := ⟨inferInstance,cost⟩

def and (p q : Prop) (a : Measured (Decidable p)) (b : Measured (Decidable q)) : Measured (Decidable (p ∧ q)) :=
  ⟨@instDecidableAnd p q a.value b.value,a.cost+b.cost+1⟩

def or (p q : Prop) (a : Measured (Decidable p)) (b : Measured (Decidable q)) : Measured (Decidable (p ∨ q)) :=
  ⟨@instDecidableOr p q a.value b.value,a.cost+b.cost+1⟩

def ofIff {p q : Prop} (h : p ↔ q) (a : Measured (Decidable p)) : Measured (Decidable q) :=
  ⟨@decidable_of_iff q p h a.value,a.cost⟩

def existsList {α : Type*} (p : α → Prop) (test : ∀ x, Measured (Decidable (p x))) :
    (xs : List α) → Measured (Decidable (∃ x ∈ xs, p x))
  | [] => ⟨isFalse (by simp),1⟩
  | x::xs =>
      let a := test x
      let b := existsList p test xs
      ofIff (by simp only [List.mem_cons]; aesop)
        (or _ _ a b)

theorem existsList_cost {α : Type*} (p : α → Prop) (test : ∀ x, Measured (Decidable (p x)))
    (xs : List α) {c : ℕ} (h : ∀ x ∈ xs, (test x).cost ≤ c) :
    (existsList p test xs).cost ≤ (c+1)*xs.length+1 := by
  induction xs with
  | nil => simp [existsList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun y hy => h y (by simp [hy]))
    simp only [existsList,ofIff,or,List.length_cons]
    nlinarith

def existsFin {n : ℕ} (p : Fin n → Prop) (test : ∀ i, Measured (Decidable (p i))) :
    Measured (Decidable (∃ i, p i)) :=
  let xs := Measured.finRange n
  let r := existsList p test xs.value
  let out := ofIff (by rw [Measured.finRange_value]; simp) r
  ⟨out.value,xs.cost+out.cost+1⟩

theorem existsFin_cost {n : ℕ} (p : Fin n → Prop) (test : ∀ i, Measured (Decidable (p i)))
    {c : ℕ} (h : ∀ i, (test i).cost ≤ c) :
    (existsFin p test).cost ≤ (n+1)^2+(c+1)*n+2 := by
  have h1 := Measured.finRange_cost n
  have h2 := existsList_cost p test (Measured.finRange n).value (fun i _ => h i)
  rw [Measured.finRange_value,List.length_finRange] at h2
  change (Measured.finRange n).cost + (existsList p test (Measured.finRange n).value).cost+1 ≤ _
  rw [Measured.finRange_value]
  omega

/-- Every measured finite decision is the same logical decision as its decidable
predicate. The clock is computational data, while this equality is a proof. -/
theorem decision_eq {p : Prop} [Decidable p] (a : Measured (Decidable p)) : a.value = (inferInstance : Decidable p) :=
  Subsingleton.elim _ _

end Decision
end TreewidthHom.Executable
