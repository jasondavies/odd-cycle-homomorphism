module
public import TreewidthHom.ExecutableSchema
@[expose] public section
namespace TreewidthHom
instance stepDecidable (a b : ℕ) : Decidable (Step a b) := inferInstanceAs (Decidable (b = a ∨ b = a+1))
end TreewidthHom
namespace TreewidthHom.LCSInstance

theorem queryEdge_iff {k N ℓ : ℕ} (r : Fin 5) (u v : QueryVertex k N ℓ) :
    QueryEdge k N ℓ r u v ↔
    (r = 0 ∧ ∃ i : Fin k, u = .anchor i.castSucc ∧ v = .anchor i.succ) ∨
    (r = 1 ∧ ∃ i : Fin k, u = .anchor i.succ ∧ v = .row i (boundary 0)) ∨
    (r = 2 ∧ ∃ i : Fin k, ∃ j : Fin ℓ, ∃ s : Fin N,
      u = .row i (.inl (j,s.castSucc)) ∧ v = .row i (.inl (j,s.succ))) ∨
    (r = 3 ∧ ∃ i : Fin k, ∃ j : Fin ℓ,
      u = .row i (.inl (j,Fin.last N)) ∧ v = .row i (boundary j.succ)) ∨
    (r = 4 ∧ ∃ i : Fin k, ∃ j : Fin ℓ, u = .row i (boundary j.succ) ∧ v = .letter j) := by
  constructor
  · intro h
    cases h <;> simp
  · rintro (⟨rfl,i,rfl,rfl⟩ | ⟨rfl,i,rfl,rfl⟩ | ⟨rfl,i,j,s,rfl,rfl⟩ |
      ⟨rfl,i,j,rfl,rfl⟩ | ⟨rfl,i,j,rfl,rfl⟩)
    · exact .next i
    · exact .begin i
    · exact .step i j s
    · exact .advance i j
    · exact .letter i j

instance queryEdgeDecidable (k N ℓ : ℕ) (r : Fin 5) : DecidableRel (QueryEdge k N ℓ r) :=
  fun u v => decidable_of_iff _ (queryEdge_iff r u v).symm

theorem targetEdge_iff {k : ℕ} (words : Fin k → List Bool) (r : Fin 5) (u v : TargetVertex words) :
    TargetEdge words r u v ↔
    (r = 0 ∧ ∃ i : Fin k, u = .anchor i.castSucc ∧ v = .anchor i.succ) ∨
    (r = 1 ∧ ∃ i : Fin k, u = .anchor i.succ ∧ v = .pos i 0) ∨
    (r = 2 ∧ ∃ i : Fin k, ∃ a b : Fin ((words i).length+1),
      Step a.val b.val ∧ u = .pos i a ∧ v = .pos i b) ∨
    (r = 3 ∧ ∃ i : Fin k, ∃ a b : Fin ((words i).length+1),
      b.val = a.val+1 ∧ u = .pos i a ∧ v = .pos i b) ∨
    (r = 4 ∧ ∃ i : Fin k, ∃ j : Fin ((words i).length),
      u = .pos i (occurrence i j) ∧ v = .bit ((words i).get j)) := by
  constructor
  · intro h
    cases h <;> simp <;> aesop
  · rintro (⟨rfl,i,rfl,rfl⟩ | ⟨rfl,i,rfl,rfl⟩ | ⟨rfl,i,a,b,h,rfl,rfl⟩ |
      ⟨rfl,i,a,b,h,rfl,rfl⟩ | ⟨rfl,i,j,rfl,rfl⟩)
    · exact .next i
    · exact .begin i
    · exact .step i a b h
    · exact .advance i a b h
    · exact .letter i j

instance targetEdgeDecidable {k : ℕ} (words : Fin k → List Bool) (r : Fin 5) :
    DecidableRel (TargetEdge words r) :=
  fun u v => decidable_of_iff _ (targetEdge_iff words r u v).symm

instance (k N ℓ : ℕ) : DecidablePred (query k N ℓ).root := fun _ => inferInstanceAs (Decidable (_ = _))
instance (k N ℓ : ℕ) (r : Fin 5) : DecidableRel ((query k N ℓ).binary r) := queryEdgeDecidable k N ℓ r
instance {k : ℕ} (words : Fin k → List Bool) : DecidablePred (target words).root :=
  fun _ => inferInstanceAs (Decidable (_ = _))
instance {k : ℕ} (words : Fin k → List Bool) (r : Fin 5) : DecidableRel ((target words).binary r) :=
  targetEdgeDecidable words r

end TreewidthHom.LCSInstance

namespace TreewidthHom.UnaryBinary
instance holdsDecidable {V : Type} (A : UnaryBinary V)
    [DecidablePred A.root] [∀ r, DecidableRel (A.binary r)] (r : Fin 6) :
    DecidablePred (A.asRelational.holds r) := by
  intro t
  unfold asRelational
  dsimp only
  split <;> infer_instance
end TreewidthHom.UnaryBinary

namespace TreewidthHom.Relational
instance vertexDecidableEq {R : Type} {arity : R → ℕ} {V : Type}
    [DecidableEq R] [DecidableEq V] (A : Relational R arity V) : DecidableEq A.Vertex :=
  A.vertexEquiv.injective.decidableEq

instance edgeDecidable {R : Type} {arity : R → ℕ} {V : Type}
    [DecidableEq R] [DecidableEq V] (A : Relational R arity V) : DecidableRel A.Edge := by
  intro u v
  cases u with
  | domain a => exact isFalse (by intro h; cases h)
  | tuple f =>
    cases v with
    | domain _ => exact isFalse (by intro h; cases h)
    | tuple _ => exact isFalse (by intro h; cases h)
    | port g i =>
      exact decidable_of_iff (f = g) ⟨by rintro rfl; exact .first _ i,by intro h; cases h; rfl⟩
  | port f i =>
    cases v with
    | tuple _ => exact isFalse (by intro h; cases h)
    | port _ _ => exact isFalse (by intro h; cases h)
    | domain a =>
      exact decidable_of_iff (f.2.val i = a) ⟨by rintro rfl; exact .second f i,by intro h; cases h; rfl⟩

instance typedEdgeDecidable {R : Type} {arity : R → ℕ} {V : Type}
    [DecidableEq R] [DecidableEq V] (A : Relational R arity V) : DecidableRel A.typedDag.edge := A.edgeDecidable
end TreewidthHom.Relational

namespace TreewidthHom.TypedDag
instance encodedEdgeDecidable {C : Type} {V : Type} [DecidableEq V]
    (A : TypedDag C V) [DecidableRel A.edge] (M : Markers C) : DecidableRel (A.EncodedEdge M) := by
  rintro ⟨u,x⟩ ⟨v,y⟩
  by_cases h : u = v
  · subst v
    exact decidable_of_iff _ (A.encoded_same_vertex M u x y).symm
  · exact decidable_of_iff (A.edge u v ∧ x = 0 ∧ y = 0)
      ⟨by rintro ⟨he,rfl,rfl⟩; exact .base he, fun he => A.encoded_cross_edge M he h⟩

instance encodedDecidable {C : Type} {V : Type} [DecidableEq V]
    (A : TypedDag C V) [DecidableRel A.edge] (M : Markers C) : DecidableRel (A.encoded M).edge :=
  A.encodedEdgeDecidable M
end TreewidthHom.TypedDag
