module

public import TreewidthHom.CycleRank
public import TreewidthHom.DirectionReduction

@[expose] public section

namespace TreewidthHom

/-- Distinct prime lengths encode a fixed collection of vertex types. -/
structure Markers (C : Type) where
  length : C → ℕ
  prime : ∀ c, (length c).Prime
  injective : Function.Injective length

instance {C : Type} (M : Markers C) (c : C) : NeZero (M.length c) := ⟨(M.prime c).ne_zero⟩
instance {C : Type} (M : Markers C) (c : C) : Fact (1 < M.length c) := ⟨(M.prime c).one_lt⟩

/-- A typed digraph with a strictly increasing rank, and differently typed arc endpoints. -/
structure TypedDag (C : Type) (V : Type*) where
  edge : V → V → Prop
  color : V → C
  rank : V → ℕ
  increases : ∀ {u v}, edge u v → rank u < rank v
  separates : ∀ {u v}, edge u v → color u ≠ color v

namespace TypedDag
variable {C : Type} {V W : Type*}

structure Hom (A : TypedDag C V) (B : TypedDag C W) where
  map : V → W
  preserve : ∀ {u v}, A.edge u v → B.edge (map u) (map v)
  colors : ∀ v, B.color (map v) = A.color v

abbrev Decorated (A : TypedDag C V) (M : Markers C) := Σ v, ZMod (M.length (A.color v))

inductive EncodedEdge (A : TypedDag C V) (M : Markers C) : A.Decorated M → A.Decorated M → Prop
  | cycle (v : V) (x : ZMod (M.length (A.color v))) : EncodedEdge A M ⟨v,x⟩ ⟨v,x+1⟩
  | base {u v : V} (h : A.edge u v) : EncodedEdge A M ⟨u,0⟩ ⟨v,0⟩

theorem encoded_same_vertex (A : TypedDag C V) (M : Markers C)
    (v : V) (x y : ZMod (M.length (A.color v))) :
    A.EncodedEdge M ⟨v,x⟩ ⟨v,y⟩ ↔ y = x+1 := by
  constructor
  · intro h
    cases h with
    | cycle => rfl
    | base h => exact False.elim ((Nat.lt_irrefl _) (A.increases h))
  · rintro rfl; exact .cycle v x

def encoded (A : TypedDag C V) (M : Markers C) : Digraph (A.Decorated M) where
  edge := A.EncodedEdge M
  loopless := by
    rintro ⟨v,x⟩ h
    have he := (A.encoded_same_vertex M v x x).mp h
    have hz : (1 : ZMod (M.length (A.color v))) = 0 := by
      exact add_left_cancel (a := x) (b := 1) (c := 0) (by simpa only [add_zero] using he.symm)
    exact one_ne_zero hz

theorem encoded_rank_mono (A : TypedDag C V) (M : Markers C)
    {x y : A.Decorated M} (h : A.EncodedEdge M x y) : A.rank x.1 ≤ A.rank y.1 := by
  cases h with
  | cycle => exact le_rfl
  | base h => exact (A.increases h).le

theorem encoded_same_component (A : TypedDag C V) (M : Markers C)
    {x y : A.Decorated M} (h : A.EncodedEdge M x y)
    (hr : A.rank x.1 = A.rank y.1) : x.1 = y.1 := by
  cases h with
  | cycle => rfl
  | base h => have hi := A.increases h; simp_all

theorem encoded_cross_edge (A : TypedDag C V) (M : Markers C)
    {x y : A.Decorated M} (h : A.EncodedEdge M x y) (hne : x.1 ≠ y.1) :
    A.edge x.1 y.1 ∧ x.2 = 0 ∧ y.2 = 0 := by
  cases h with
  | cycle => exact False.elim (hne rfl)
  | base h => exact ⟨h,rfl,rfl⟩

namespace EncodedHom
variable {A : TypedDag C V} {B : TypedDag C W} {M : Markers C}
variable (f : Digraph.Hom (A.encoded M) (B.encoded M))

/-- Every source marker cycle remains in a single target component. -/
theorem component (v : V) (x : ZMod (M.length (A.color v))) :
    (f ⟨v,x⟩).1 = (f ⟨v,0⟩).1 := by
  have hr := cycle_rank_constant (M.length (A.color v))
    (fun x => B.rank (f ⟨v,x⟩).1)
    (fun x => B.encoded_rank_mono M (f.map_rel' (.cycle v x)))
  have hs : ∀ x : ZMod (M.length (A.color v)), (f ⟨v,x+1⟩).1 = (f ⟨v,x⟩).1 := by
    intro x
    exact (B.encoded_same_component M (f.map_rel' (.cycle v x))
      ((hr x).trans (hr (x+1)).symm)).symm
  have hn : ∀ n : ℕ, (f ⟨v,(n : ZMod (M.length (A.color v)))⟩).1 = (f ⟨v,0⟩).1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa [Nat.cast_add, hs] using ih
  simpa using hn x.val

def localMap (v : V) (x : ZMod (M.length (A.color v))) :
    ZMod (M.length (B.color (f ⟨v,0⟩).1)) :=
  (component f v x) ▸ (f ⟨v,x⟩).2

theorem image_eq (v : V) (x : ZMod (M.length (A.color v))) :
    f ⟨v,x⟩ = ⟨(f ⟨v,0⟩).1,localMap f v x⟩ := by
  exact Sigma.eq (component f v x) (by simp [localMap])

theorem localMap_cycle (v : V) :
    CycleHom (M.length (A.color v)) (M.length (B.color (f ⟨v,0⟩).1)) (localMap f v) := by
  intro x
  have he := f.map_rel' (.cycle v x)
  change B.EncodedEdge M (f ⟨v,x⟩) (f ⟨v,x+1⟩) at he
  rw [image_eq f v x, image_eq f v (x+1)] at he
  exact (B.encoded_same_vertex M _ _ _).mp he

/-- Distinct prime markers force preservation of vertex types. -/
theorem colors (v : V) : B.color (f ⟨v,0⟩).1 = A.color v := by
  apply M.injective
  exact (prime_cycleHom_eq (M.prime (A.color v)) (M.prime (B.color (f ⟨v,0⟩).1))
    (localMap f v) (localMap_cycle f v)).symm

/-- Project the image of each root to its target component. -/
def recover : Hom A B where
  map v := (f ⟨v,0⟩).1
  colors := colors f
  preserve := by
    intro u v h
    apply (B.encoded_cross_edge M (f.map_rel' (.base h)) ?_).1
    intro he
    apply A.separates h
    exact (colors f u).symm.trans ((congrArg B.color he).trans (colors f v))

end EncodedHom

namespace Hom
variable {A : TypedDag C V} {B : TypedDag C W} (f : Hom A B) (M : Markers C)

def cycleEquiv (v : V) : ZMod (M.length (A.color v)) ≃+* ZMod (M.length (B.color (f.map v))) :=
  ZMod.ringEquivCongr (congrArg M.length (f.colors v).symm)

def extend : Digraph.Hom (A.encoded M) (B.encoded M) where
  toFun z := ⟨f.map z.1, cycleEquiv f M z.1 z.2⟩
  map_rel' := by
    intro x y h
    cases h with
    | cycle v x =>
      simp only [map_add, map_one]
      exact .cycle _ _
    | base h =>
      simp only [map_zero]
      exact .base (f.preserve h)

end Hom

/-- Erasing vertex types by prime cycles preserves homomorphism existence. -/
theorem colorEncoding_iff (A : TypedDag C V) (B : TypedDag C W) (M : Markers C) :
    Nonempty (Digraph.Hom (A.encoded M) (B.encoded M)) ↔ Nonempty (Hom A B) := by
  constructor
  · rintro ⟨f⟩; exact ⟨EncodedHom.recover f⟩
  · rintro ⟨f⟩; exact ⟨f.extend M⟩

/-- Every decorated vertex has an outgoing cycle arc. -/
theorem encoded_noIsolated (A : TypedDag C V) (M : Markers C) : (A.encoded M).NoIsolated := by
  rintro ⟨v,x⟩
  exact ⟨⟨v,x+1⟩,Or.inl (.cycle v x)⟩

end TypedDag
end TreewidthHom
