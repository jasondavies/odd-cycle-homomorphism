module

public import TreewidthHom.RelationalReduction

@[expose] public section

namespace TreewidthHom.Relational
variable {R : Type} {arity : R → ℕ}

def tagEquiv : Tag R arity ≃ (Unit ⊕ (Σ r, Unit ⊕ Fin (arity r))) where
  toFun
    | .domain => .inl ()
    | .tuple r => .inr ⟨r,.inl ()⟩
    | .port r i => .inr ⟨r,.inr i⟩
  invFun
    | .inl _ => .domain
    | .inr ⟨r,.inl _⟩ => .tuple r
    | .inr ⟨r,.inr i⟩ => .port r i
  left_inv := by intro t; cases t <;> rfl
  right_inv := by
    rintro (u | ⟨r,u | i⟩)
    · cases u; rfl
    · cases u; rfl
    · rfl

instance [Fintype R] : Fintype (Tag R arity) := Fintype.ofEquiv _ tagEquiv.symm
instance [DecidableEq R] : DecidableEq (Tag R arity) := tagEquiv.injective.decidableEq

/-- Root is unary; Next, Begin, Step, Advance and Letter are binary. -/
def schemaArity (r : Fin 6) : ℕ := if r = 0 then 1 else 2

theorem schema_tags_card : Fintype.card (Tag (Fin 6) schemaArity) = 18 := by
  rw [Fintype.card_congr tagEquiv]
  decide

end TreewidthHom.Relational

namespace TreewidthHom

noncomputable def markerIndex (C : Type) [Fintype C] (h : Fintype.card C ≤ 18) (c : C) :
    Fin markerPrimes.length :=
  ⟨(Fintype.equivFin C c).val, by have hi := (Fintype.equivFin C c).isLt; rw [markerPrimes_length]; omega⟩

/-- Instantiate any at-most-18 vertex types with the actual marker-prime list. -/
noncomputable def standardMarkers (C : Type) [Fintype C] (h : Fintype.card C ≤ 18) : Markers C where
  length c := markerPrimes.get (markerIndex C h c)
  prime c := markerPrimes_prime _ (List.get_mem _ _)
  injective := by
    intro a b hab
    have hi := markerPrimes_nodup.injective_get hab
    apply (Fintype.equivFin C).injective
    apply Fin.ext
    simpa only [markerIndex] using congrArg (fun i : Fin markerPrimes.length => i.val) hi

theorem standardMarkers_bound (C : Type) [Fintype C] (h : Fintype.card C ≤ 18) (c : C) :
    (standardMarkers C h).length c ≤ 67 := by
  have hb : ∀ p ∈ markerPrimes, p ≤ 67 := by decide
  exact hb _ (List.get_mem _ _)

/-- The fixed six-relation schema needs exactly the 18 prime markers. -/
noncomputable def schemaMarkers : Markers (Relational.Tag (Fin 6) Relational.schemaArity) :=
  standardMarkers _ (le_of_eq Relational.schema_tags_card)

end TreewidthHom
