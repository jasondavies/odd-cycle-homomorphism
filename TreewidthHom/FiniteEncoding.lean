module

public import TreewidthHom.LCSReduction

@[expose] public section

namespace TreewidthHom.Relational
variable {R : Type} {arity : R → ℕ} {V : Type*}

def vertexEquiv (A : Relational R arity V) :
    A.Vertex ≃ (V ⊕ (Σ f : A.Fact, Unit ⊕ Fin (arity f.1))) where
  toFun
    | .domain v => .inl v
    | .tuple f => .inr ⟨f,.inl ()⟩
    | .port f i => .inr ⟨f,.inr i⟩
  invFun
    | .inl v => .domain v
    | .inr ⟨f,.inl _⟩ => .tuple f
    | .inr ⟨f,.inr i⟩ => .port f i
  left_inv := by intro v; cases v <;> rfl
  right_inv := by
    rintro (v | ⟨f,u | i⟩)
    · rfl
    · cases u; rfl
    · rfl

noncomputable instance factFintype [Fintype R] [Fintype V] (A : Relational R arity V) :
    Fintype A.Fact := by
  classical
  exact Sigma.instFintype

noncomputable instance vertexFintype [Fintype R] [Fintype V] (A : Relational R arity V) :
    Fintype A.Vertex := Fintype.ofEquiv _ (vertexEquiv A).symm

theorem fact_card_le [Fintype R] [Fintype V] (A : Relational R arity V)
    (ha : ∀ r, arity r ≤ 2) :
    Fintype.card A.Fact ≤ Fintype.card R * (Fintype.card V + 1)^2 := by
  classical
  rw [show Fintype.card A.Fact = ∑ r : R, Fintype.card {t : Fin (arity r) → V // A.holds r t}
    from Fintype.card_sigma]
  calc
    _ ≤ ∑ r : R, (Fintype.card V + 1)^2 := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _ ≤ Fintype.card (Fin (arity r) → V) := Fintype.card_subtype_le _
        _ = Fintype.card V ^ arity r := by simp
        _ ≤ (Fintype.card V + 1) ^ arity r := Nat.pow_le_pow_left (show Fintype.card V ≤ Fintype.card V + 1 by omega) (arity r)
        _ ≤ (Fintype.card V + 1)^2 := Nat.pow_le_pow_right (by omega) (ha r)
    _ = _ := by simp

theorem vertex_card_le [Fintype R] [Fintype V] (A : Relational R arity V)
    (ha : ∀ r, arity r ≤ 2) :
    Fintype.card A.Vertex ≤ Fintype.card V + 3 * Fintype.card A.Fact := by
  rw [Fintype.card_congr (vertexEquiv A), Fintype.card_sum, Fintype.card_sigma]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ f : A.Fact, 3 := by
      apply Finset.sum_le_sum
      intro f _
      simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
      have := ha f.1
      omega
    _ = _ := by simp [Nat.mul_comm]

end TreewidthHom.Relational

namespace TreewidthHom
noncomputable instance digraphArcFintype {V : Type*} [Fintype V] (D : Digraph V) :
    Fintype D.Arc := Fintype.ofFinite _

instance decoratedFintype {C : Type} {V : Type*} [Fintype V]
    (A : TypedDag C V) (M : Markers C) : Fintype (A.Decorated M) :=
  inferInstanceAs (Fintype (Σ v, ZMod (M.length (A.color v))))

theorem decorated_card_le {C : Type} {V : Type*} [Fintype V]
    (A : TypedDag C V) (M : Markers C) {m : ℕ} (hm : ∀ c, M.length c ≤ m) :
    Fintype.card (A.Decorated M) ≤ m * Fintype.card V := by
  rw [show Fintype.card (A.Decorated M) = ∑ v : V, Fintype.card (ZMod (M.length (A.color v)))
    from Fintype.card_sigma]
  calc
    _ ≤ ∑ v : V, m := by
      apply Finset.sum_le_sum
      intro v _
      simpa using hm (A.color v)
    _ = _ := by simp [Nat.mul_comm]

/-- A coarse polynomial bound independent of the relations' interpretation.
It counts every possible arc; the executable sparse construction is smaller. -/
theorem schema_graph_card_le {V : Type*} [Fintype V]
    (A : Relational (Fin 6) Relational.schemaArity V) :
    Fintype.card (Arrow.AssemblyVertex (A.typedDag.Decorated schemaMarkers)
      (A.typedDag.encoded schemaMarkers).Arc) ≤ 20000000 * (Fintype.card V + 1)^4 := by
  have ha : ∀ r : Fin 6, Relational.schemaArity r ≤ 2 := by
    intro r; unfold Relational.schemaArity; split <;> omega
  have hf := A.fact_card_le ha
  have hv := A.vertex_card_le ha
  simp only [Fintype.card_fin] at hf
  have hd := decorated_card_le A.typedDag schemaMarkers
    (fun c => standardMarkers_bound _ _ c)
  let n := Fintype.card V
  let d := Fintype.card (A.typedDag.Decorated schemaMarkers)
  have hdb : d ≤ 1273 * (n+1)^2 := by
    dsimp [d,n]
    nlinarith [sq_nonneg (Fintype.card V : ℤ)]
  have harc : Fintype.card (A.typedDag.encoded schemaMarkers).Arc ≤ d^2 := by
    calc
      _ ≤ Fintype.card (A.typedDag.Decorated schemaMarkers × A.typedDag.Decorated schemaMarkers) :=
        Fintype.card_subtype_le _
      _ = d^2 := by simp [d,pow_two]
  rw [Digraph.directionReduction_card]
  change d + 11 * Fintype.card (A.typedDag.encoded schemaMarkers).Arc ≤ 20000000 * (n+1)^4
  have hsq : d^2 ≤ (1273 * (n+1)^2)^2 := Nat.pow_le_pow_left hdb 2
  have hn : (n+1)^2 ≤ (n+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

end TreewidthHom

namespace TreewidthHom.LCSInstance

def queryEquiv (k N ℓ : ℕ) :
    QueryVertex k N ℓ ≃ (Fin (k+1) ⊕ ((Fin k × Position N ℓ) ⊕ Fin ℓ)) where
  toFun
    | .anchor i => .inl i
    | .row i p => .inr (.inl (i,p))
    | .letter j => .inr (.inr j)
  invFun
    | .inl i => .anchor i
    | .inr (.inl (i,p)) => .row i p
    | .inr (.inr j) => .letter j
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (i | ⟨i,p⟩ | j) <;> rfl

instance queryFintype (k N ℓ : ℕ) : Fintype (QueryVertex k N ℓ) :=
  Fintype.ofEquiv _ (queryEquiv k N ℓ).symm

def targetEquiv {k : ℕ} (words : Fin k → List Bool) :
    TargetVertex words ≃ (Fin (k+1) ⊕ ((Σ i, Fin ((words i).length+1)) ⊕ Bool)) where
  toFun
    | .anchor i => .inl i
    | .pos i p => .inr (.inl ⟨i,p⟩)
    | .bit b => .inr (.inr b)
  invFun
    | .inl i => .anchor i
    | .inr (.inl ⟨i,p⟩) => .pos i p
    | .inr (.inr b) => .bit b
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (i | ⟨i,p⟩ | b) <;> rfl

instance targetFintype {k : ℕ} (words : Fin k → List Bool) : Fintype (TargetVertex words) :=
  Fintype.ofEquiv _ (targetEquiv words).symm

theorem query_card (k N ℓ : ℕ) :
    Fintype.card (QueryVertex k N ℓ) = (k+1) + k*(ℓ*(N+1)+1) + ℓ := by
  rw [Fintype.card_congr (queryEquiv k N ℓ)]
  simp [Position,Fintype.card_sum,Fintype.card_prod,Nat.add_assoc]

theorem target_card {k : ℕ} (words : Fin k → List Bool) :
    Fintype.card (TargetVertex words) = (k+1) + (∑ i, ((words i).length+1)) + 2 := by
  rw [Fintype.card_congr (targetEquiv words)]
  simp [Fintype.card_sum,Fintype.card_sigma,Nat.add_assoc]

end TreewidthHom.LCSInstance
