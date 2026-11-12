module
public import TreewidthHom.MeasuredSchema
@[expose] public section
namespace TreewidthHom.Executable
open LCSInstance EnumRun

structure InputStats where
  count : ℕ
  total : ℕ
  short : Bool
  deriving Repr, DecidableEq

/-- One pass over the input, measuring the word-length traversals explicitly.
The requested length comparison is a supplied primitive of cost q. -/
def statsMeasured (q ℓ : ℕ) : List (List Bool) → Measured InputStats
  | [] => ⟨⟨0,0,false⟩,1⟩
  | w::xs =>
    let n := lengthMeasured w
    let r := statsMeasured q ℓ xs
    ⟨⟨r.value.count+1,r.value.total+n.value,decide (n.value<ℓ)||r.value.short⟩,
      n.cost+r.cost+q+5⟩

theorem statsMeasured_spec (q ℓ : ℕ) (xs : List (List Bool)) :
    (statsMeasured q ℓ xs).value.count = xs.length ∧
    (statsMeasured q ℓ xs).value.total = (xs.map List.length).sum ∧
    ((statsMeasured q ℓ xs).value.short = true ↔ ∃ w ∈ xs, w.length < ℓ) ∧
    (statsMeasured q ℓ xs).cost = (xs.map List.length).sum+(q+6)*xs.length+1 := by
  induction xs with
  | nil => simp [statsMeasured]
  | cons w xs ih =>
    rcases ih with ⟨hc,ht,hs,hr⟩
    simp only [statsMeasured,(lengthMeasured_spec w).1,(lengthMeasured_spec w).2, hc,ht,hr,List.length_cons,List.map_cons,List.sum_cons,
      Bool.or_eq_true,decide_eq_true_eq,hs,List.mem_cons]
    constructor
    · trivial
    constructor
    · omega
    constructor
    · constructor
      · rintro (h | ⟨v,hv,h⟩)
        · exact ⟨w,Or.inl rfl,h⟩
        · exact ⟨v,Or.inr hv,h⟩
      · rintro ⟨v,hv,h⟩
        rcases hv with rfl | hv
        · exact Or.inl h
        · exact Or.inr ⟨v,hv,h⟩
    · nlinarith

theorem totalLength_get (xs : List (List Bool)) : totalLength xs.get = (xs.map List.length).sum := by
  unfold totalLength
  rw [← List.sum_ofFn]
  congr 1
  change List.ofFn (List.length ∘ xs.get) = _
  rw [← List.map_ofFn,List.ofFn_get]

theorem statsMeasured_short (q ℓ : ℕ) (xs : List (List Bool)) :
    (statsMeasured q ℓ xs).value.short = true ↔ ∃ i : Fin xs.length, (xs.get i).length < ℓ := by
  rw [(statsMeasured_spec q ℓ xs).2.2.1]
  constructor
  · rintro ⟨w,hw,h⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hw
    exact ⟨i,h⟩
  · rintro ⟨i,h⟩
    exact ⟨xs.get i,xs.get_mem i,h⟩

theorem statsMeasured_level {q ℓ s : ℕ} (xs : List (List Bool))
    (hk : xs.length ≤ s) (hN : totalLength xs.get ≤ s) (hq : q ≤ s+1) :
    (statsMeasured q ℓ xs).cost ≤ budget 1 s := by
  rw [(statsMeasured_spec q ℓ xs).2.2.2,← totalLength_get]
  change _ ≤ grow (s+1)
  have hm := Nat.mul_le_mul (Nat.add_le_add_right hq 6) hk
  unfold grow
  nlinarith [sq_nonneg (s : ℤ)]

end TreewidthHom.Executable
