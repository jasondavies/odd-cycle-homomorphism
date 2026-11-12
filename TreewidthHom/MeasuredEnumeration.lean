module
public import TreewidthHom.MeasuredLists
@[expose] public section
namespace TreewidthHom.Executable

/-- Instrumented execution of a particular explicit enumeration. Mapping callbacks
are one-step primitives in this abstract model. Their internal implementation
cost must be justified separately before inferring a bit-time bound. -/
structure EnumRun {α : Type*} (e : Enumeration α) where
  run : Measured (List α)
  correct : run.value = e.elems

namespace EnumRun
open Enumeration
variable {α β : Type*}

def fin (n : ℕ) : EnumRun (Enumeration.fin n) := ⟨Measured.finRange n,Measured.finRange_value n⟩
def unit : EnumRun Enumeration.unit := ⟨⟨[()],2⟩,rfl⟩
def bool : EnumRun Enumeration.bool := ⟨⟨[false,true],3⟩,rfl⟩

def map {e : Enumeration α} (a : EnumRun e) (f : α ≃ β) : EnumRun (e.map f) where
  run := let b := Measured.mapList (fun x => Measured.step (f x)) a.run.value
         ⟨b.value,a.run.cost+b.cost+1⟩
  correct := by simp [Measured.mapList_value,Measured.step,a.correct,Enumeration.map]

theorem map_cost {e : Enumeration α} (a : EnumRun e) (f : α ≃ β) :
    (a.map f).run.cost ≤ a.run.cost+2*e.elems.length+2 := by
  have h := Measured.mapList_cost (fun x => Measured.step (f x)) a.run.value
    (c := 1) (by intro _ _; exact le_rfl)
  rw [a.correct] at h
  dsimp only [map]
  rw [a.correct]
  nlinarith

def sum {e : Enumeration α} {f : Enumeration β} (a : EnumRun e) (b : EnumRun f) : EnumRun (e.sum f) where
  run :=
    let l := Measured.mapList (fun x => Measured.step (Sum.inl x : α ⊕ β)) a.run.value
    let r := Measured.mapList (fun x => Measured.step (Sum.inr x : α ⊕ β)) b.run.value
    let z := Measured.appendList l.value r.value
    ⟨z.value,a.run.cost+b.run.cost+l.cost+r.cost+z.cost+1⟩
  correct := by simp [Measured.appendList_spec,Measured.mapList_value,Measured.step,a.correct,b.correct,Enumeration.sum]

theorem sum_cost {e : Enumeration α} {f : Enumeration β} (a : EnumRun e) (b : EnumRun f) :
    (a.sum b).run.cost ≤ a.run.cost+b.run.cost+3*e.elems.length+2*f.elems.length+4 := by
  have hl := Measured.mapList_cost (fun x => Measured.step (Sum.inl x : α ⊕ β)) a.run.value
    (c := 1) (by intro _ _; exact le_rfl)
  have hr := Measured.mapList_cost (fun x => Measured.step (Sum.inr x : α ⊕ β)) b.run.value
    (c := 1) (by intro _ _; exact le_rfl)
  rw [a.correct] at hl
  rw [b.correct] at hr
  simp only [sum,(Measured.appendList_spec _ _).2,Measured.mapList_value,List.length_map,a.correct,b.correct]
  nlinarith

def sigma {ι : Type*} {δ : ι → Type*} {e : Enumeration ι} {f : ∀ i, Enumeration (δ i)}
    (a : EnumRun e) (b : ∀ i, EnumRun (f i)) : EnumRun (Enumeration.sigma e f) where
  run :=
    let z := Measured.flatMapList (fun i =>
      let r := Measured.mapList (fun x => Measured.step (Sigma.mk i x)) (b i).run.value
      ⟨r.value,(b i).run.cost+r.cost+1⟩) a.run.value
    ⟨z.value,a.run.cost+z.cost+1⟩
  correct := by simp [Measured.flatMapList_value,Measured.mapList_value,Measured.step,a.correct,fun i => (b i).correct,Enumeration.sigma]

theorem sigma_cost {ι : Type*} {δ : ι → Type*} {e : Enumeration ι} {f : ∀ i, Enumeration (δ i)}
    (a : EnumRun e) (b : ∀ i, EnumRun (f i)) {c m : ℕ}
    (hc : ∀ i, (b i).run.cost ≤ c) (hm : ∀ i, (f i).elems.length ≤ m) :
    (sigma a b).run.cost ≤ a.run.cost+(c+3*m+4)*e.elems.length+2 := by
  let body := fun i =>
      let r := Measured.mapList (fun x => Measured.step (Sigma.mk i x)) (b i).run.value
      (⟨r.value,(b i).run.cost+r.cost+1⟩ : Measured (List (Σ i, δ i)))
  have hb : ∀ i ∈ a.run.value, (body i).cost ≤ c+2*m+2 := by
    intro i _
    have h := Measured.mapList_cost (fun x => Measured.step (Sigma.mk i x)) (b i).run.value
      (c := 1) (by intro _ _; exact le_rfl)
    rw [(b i).correct] at h
    have hi := hc i
    have hj := hm i
    simp only [body]
    rw [(b i).correct]
    nlinarith
  have hl : ∀ i ∈ a.run.value, (body i).value.length ≤ m := by
    intro i _
    simpa [body,Measured.mapList_value,(b i).correct] using hm i
  have h := Measured.flatMapList_cost body a.run.value hb hl
  rw [a.correct] at h
  change a.run.cost+(Measured.flatMapList body a.run.value).cost+1 ≤ _
  rw [a.correct]
  nlinarith

def prod {e : Enumeration α} {f : Enumeration β} (a : EnumRun e) (b : EnumRun f) : EnumRun (e.prod f) :=
  (sigma a (fun _ => b)).map (Equiv.sigmaEquivProd α β)

def testOption {p : α → Prop} (test : ∀ x, Measured (Decidable (p x))) (x : α) :
    Measured (Option {x // p x}) :=
  let r := test x
  match r.value with
  | .isTrue h => ⟨some ⟨x,h⟩,r.cost+1⟩
  | .isFalse _ => ⟨none,r.cost+1⟩

theorem testOption_value {p : α → Prop} [DecidablePred p]
    (test : ∀ x, Measured (Decidable (p x))) (x : α) :
    (testOption test x).value = if h : p x then some ⟨x,h⟩ else none := by
  by_cases h : p x
  · have hd : (test x).value = isTrue h := Subsingleton.elim _ _
    simp [testOption,hd,h]
  · have hd : (test x).value = isFalse h := Subsingleton.elim _ _
    simp [testOption,hd,h]

theorem testOption_cost {p : α → Prop} (test : ∀ x, Measured (Decidable (p x))) (x : α) :
    (testOption test x).cost = (test x).cost+1 := by
  classical
  by_cases h : p x
  · have hd : (test x).value = isTrue h := Subsingleton.elim _ _
    simp [testOption,hd]
  · have hd : (test x).value = isFalse h := Subsingleton.elim _ _
    simp [testOption,hd]

def subtype {e : Enumeration α} (a : EnumRun e) (p : α → Prop) [DecidablePred p]
    (test : ∀ x, Measured (Decidable (p x))) : EnumRun (e.subtype p) where
  run := let z := Measured.filterMapList (testOption test) a.run.value
         ⟨z.value,a.run.cost+z.cost+1⟩
  correct := by
    simp [Measured.filterMapList_value,testOption_value,a.correct,Enumeration.subtype]

theorem subtype_cost {e : Enumeration α} (a : EnumRun e) (p : α → Prop) [DecidablePred p]
    (test : ∀ x, Measured (Decidable (p x))) {c : ℕ} (hc : ∀ x, (test x).cost ≤ c) :
    (a.subtype p test).run.cost ≤ a.run.cost+(c+3)*e.elems.length+2 := by
  have h := Measured.filterMapList_cost (testOption test) a.run.value
    (c := c+1) (by intro x _; rw [testOption_cost]; exact Nat.add_le_add_right (hc x) 1)
  rw [a.correct] at h
  dsimp only [subtype]
  rw [a.correct]
  nlinarith

end EnumRun
end TreewidthHom.Executable
