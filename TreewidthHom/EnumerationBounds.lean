module
public import TreewidthHom.MeasuredEnumeration
@[expose] public section
namespace TreewidthHom.Executable
namespace Enumeration
variable {α β : Type*}
@[simp] theorem length_fin (n : ℕ) : (fin n).elems.length = n := by simp [fin]
@[simp] theorem length_unit : unit.elems.length = 1 := rfl
@[simp] theorem length_bool : bool.elems.length = 2 := rfl
@[simp] theorem length_map (a : Enumeration α) (f : α ≃ β) : (a.map f).elems.length = a.elems.length := by simp [map]
@[simp] theorem length_sum (a : Enumeration α) (b : Enumeration β) :
    (a.sum b).elems.length = a.elems.length+b.elems.length := by simp [sum]
@[simp] theorem length_prod (a : Enumeration α) (b : Enumeration β) :
    (a.prod b).elems.length = a.elems.length*b.elems.length := by
  simp [prod,sigma,map,List.length_flatMap]

theorem length_sigma_le {ι : Type*} {δ : ι → Type*} (a : Enumeration ι)
    (b : ∀ i, Enumeration (δ i)) {m : ℕ} (hm : ∀ i, (b i).elems.length ≤ m) :
    (sigma a b).elems.length ≤ a.elems.length*m := by
  simp only [sigma,List.length_flatMap,List.length_map]
  calc
    _ ≤ (a.elems.map (fun _ => m)).sum := List.sum_le_sum (fun i _ => hm i)
    _ = _ := by simp

theorem length_subtype_le (a : Enumeration α) (p : α → Prop) [DecidablePred p] :
    (a.subtype p).elems.length ≤ a.elems.length := List.length_filterMap_le _ _

end Enumeration

namespace EnumRun
variable {α β : Type*}

def Bounded {e : Enumeration α} (a : EnumRun e) (b : ℕ) : Prop :=
  e.elems.length ≤ b ∧ a.run.cost ≤ b

/-- A uniform polynomial bound large enough for every enumeration combinator. -/
def grow (b : ℕ) : ℕ := 100*(b+1)^3

theorem le_grow (b : ℕ) : b ≤ grow b := by unfold grow; nlinarith [sq_nonneg (b : ℤ)]
theorem grow_mono {a b : ℕ} (h : a ≤ b) : grow a ≤ grow b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3)

theorem Bounded.mono {e : Enumeration α} {a : EnumRun e} {b c : ℕ}
    (h : a.Bounded b) (hc : b ≤ c) : a.Bounded c := ⟨h.1.trans hc,h.2.trans hc⟩

theorem bounded_fin {n b : ℕ} (h : n ≤ b) : (fin n).Bounded (grow b) := by
  have h1 := Measured.finRange_cost n
  have h2 := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
  constructor
  · simpa using h.trans (le_grow b)
  · change (Measured.finRange n).cost ≤ _
    unfold grow
    nlinarith [sq_nonneg (b : ℤ)]

theorem bounded_map {e : Enumeration α} {a : EnumRun e} {b : ℕ} (h : a.Bounded b)
    (f : α ≃ β) : (a.map f).Bounded (grow b) := by
  have hc := a.map_cost f
  constructor
  · simpa using h.1.trans (le_grow b)
  · have hl := h.1; have ht := h.2
    unfold grow
    nlinarith [sq_nonneg (b : ℤ)]

theorem bounded_sum {e : Enumeration α} {f : Enumeration β} {a : EnumRun e} {a' : EnumRun f}
    {b : ℕ} (h : a.Bounded b) (h' : a'.Bounded b) : (a.sum a').Bounded (grow b) := by
  have hc := a.sum_cost a'
  have h1 := h.1; have h2 := h.2; have h3 := h'.1; have h4 := h'.2
  constructor
  · simp only [Enumeration.length_sum]
    unfold grow
    nlinarith [sq_nonneg (b : ℤ)]
  · unfold grow
    nlinarith [sq_nonneg (b : ℤ)]

theorem bounded_sigma {ι : Type*} {δ : ι → Type*} {e : Enumeration ι} {f : ∀ i, Enumeration (δ i)}
    {a : EnumRun e} {a' : ∀ i, EnumRun (f i)} {b : ℕ}
    (h : a.Bounded b) (h' : ∀ i, (a' i).Bounded b) : (sigma a a').Bounded (grow b) := by
  have hc := sigma_cost a a' (fun i => (h' i).2) (fun i => (h' i).1)
  have hl := Enumeration.length_sigma_le e f (fun i => (h' i).1)
  have h1 := h.1; have h2 := h.2
  have hm := Nat.mul_le_mul_right b h1
  constructor <;> unfold grow
  · nlinarith [sq_nonneg (b : ℤ)]
  · have hm' := Nat.mul_le_mul_left (b+3*b+4) h1
    nlinarith [sq_nonneg (b : ℤ)]

theorem bounded_prod {e : Enumeration α} {f : Enumeration β} {a : EnumRun e} {a' : EnumRun f}
    {b : ℕ} (h : a.Bounded b) (h' : a'.Bounded b) : (a.prod a').Bounded (grow (grow b)) :=
  bounded_map (bounded_sigma h (fun _ => h')) _

theorem bounded_subtype {e : Enumeration α} {a : EnumRun e} {b : ℕ} (h : a.Bounded b)
    (p : α → Prop) [DecidablePred p] (test : ∀ x, Measured (Decidable (p x)))
    (ht : ∀ x, (test x).cost ≤ b) : (a.subtype p test).Bounded (grow b) := by
  have hc := subtype_cost a p test ht
  have h1 := h.1; have h2 := h.2
  constructor
  · exact (Enumeration.length_subtype_le e p).trans (h1.trans (le_grow b))
  · have hm := Nat.mul_le_mul_left (b+3) h1
    unfold grow
    nlinarith [sq_nonneg (b : ℤ)]

/-- Iterating a fixed number of polynomial bounds remains a polynomial. -/
def budget : ℕ → ℕ → ℕ
  | 0,s => s+1
  | n+1,s => grow (budget n s)

theorem budget_step (n s : ℕ) : budget n s ≤ budget (n+1) s := le_grow _
theorem budget_mono {n m : ℕ} (h : n ≤ m) (s : ℕ) : budget n s ≤ budget m s := by
  induction h with
  | refl => exact le_rfl
  | @step m h ih => exact ih.trans (budget_step m s)

theorem budget_polynomial (n : ℕ) : ∃ p : Polynomial ℕ, ∀ s, budget n s = p.eval s := by
  induction n with
  | zero => exact ⟨Polynomial.X+1,by intro s; simp [budget]⟩
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨Polynomial.C 100*(p+1)^3,by intro s; simp [budget,grow,hp]⟩

end EnumRun
end TreewidthHom.Executable
