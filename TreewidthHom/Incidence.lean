module

public import TreewidthHom.DirectionReduction

@[expose] public section

/-! # Typed incidence encoding of arbitrary finite-arity relational structures -/
namespace TreewidthHom

structure Relational (R : Type) (arity : R → ℕ) (V : Type*) where
  holds : ∀ r, (Fin (arity r) → V) → Prop

namespace Relational
variable {R : Type} {arity : R → ℕ} {V W : Type*}

abbrev Fact (A : Relational R arity V) := Σ r, {t : Fin (arity r) → V // A.holds r t}

inductive Vertex (A : Relational R arity V)
  | domain : V → Vertex A
  | tuple : A.Fact → Vertex A
  | port : (f : A.Fact) → Fin (arity f.1) → Vertex A

inductive Tag (R : Type) (arity : R → ℕ)
  | domain : Tag R arity
  | tuple : R → Tag R arity
  | port : (r : R) → Fin (arity r) → Tag R arity

def tag (A : Relational R arity V) : A.Vertex → Tag R arity
  | .domain _ => .domain
  | .tuple f => .tuple f.1
  | .port f i => .port f.1 i

inductive Edge (A : Relational R arity V) : A.Vertex → A.Vertex → Prop
  | first (f : A.Fact) (i : Fin (arity f.1)) : Edge A (.tuple f) (.port f i)
  | second (f : A.Fact) (i : Fin (arity f.1)) : Edge A (.port f i) (.domain (f.2.val i))

def incidence (A : Relational R arity V) : Digraph A.Vertex where
  edge := A.Edge
  loopless := by intro v h; cases h

structure Hom (A : Relational R arity V) (B : Relational R arity W) where
  map : V → W
  preserve : ∀ r t, A.holds r t → B.holds r (map ∘ t)

structure TypedHom (A : Relational R arity V) (B : Relational R arity W) where
  map : A.Vertex → B.Vertex
  preserve : ∀ {x y}, A.Edge x y → B.Edge (map x) (map y)
  tags : ∀ x, B.tag (map x) = A.tag x

def mapFact {A : Relational R arity V} {B : Relational R arity W}
    (f : Hom A B) (t : A.Fact) : B.Fact :=
  ⟨t.1, ⟨f.map ∘ t.2.val, f.preserve t.1 t.2.val t.2.prop⟩⟩

def mapVertex {A : Relational R arity V} {B : Relational R arity W}
    (f : Hom A B) : A.Vertex → B.Vertex
  | .domain v => .domain (f.map v)
  | .tuple t => .tuple (mapFact f t)
  | .port t i => .port (mapFact f t) i

/-- A structural homomorphism extends over fact and ordered-port vertices. -/
def liftHom {A : Relational R arity V} {B : Relational R arity W}
    (f : Hom A B) : TypedHom A B where
  map := mapVertex f
  preserve := by intro x y h; cases h; exact .first _ _; exact .second _ _
  tags := by intro x; cases x <;> rfl

theorem first_target {A : Relational R arity V} {p : A.Fact} {y : A.Vertex}
    (h : A.Edge (.tuple p) y) : ∃ i, y = .port p i := by
  cases h with
  | first p i => exact ⟨i,rfl⟩

theorem second_target {A : Relational R arity V} {p : A.Fact}
    {i : Fin (arity p.1)} {y : A.Vertex}
    (h : A.Edge (.port p i) y) : y = .domain (p.2.val i) := by
  cases h
  rfl

namespace TypedHom
variable {A : Relational R arity V} {B : Relational R arity W} (f : TypedHom A B)

theorem domain_image (v : V) : ∃ w, f.map (.domain v) = .domain w := by
  have h := f.tags (.domain v)
  cases he : f.map (.domain v) with
  | domain w => exact ⟨w,rfl⟩
  | tuple t => simp [he,tag] at h
  | port t i => simp [he,tag] at h

theorem tuple_image (r : R) (t : Fin (arity r) → V) (ht : A.holds r t) :
    ∃ s, ∃ hs : B.holds r s,
      f.map (.tuple ⟨r,⟨t,ht⟩⟩) = .tuple ⟨r,⟨s,hs⟩⟩ := by
  have h := f.tags (.tuple ⟨r,⟨t,ht⟩⟩)
  cases he : f.map (.tuple ⟨r,⟨t,ht⟩⟩) with
  | domain w => simp [he,tag] at h
  | port p i => simp [he,tag] at h
  | tuple p =>
    obtain ⟨r',s,hs⟩ := p
    have hr : r' = r := by simpa [he,tag] using h
    subst r'
    exact ⟨s,hs,rfl⟩

/-- Ordered port tags recover each argument of each target fact. -/
theorem recover (f : TypedHom A B) : Nonempty (Hom A B) := by
  classical
  choose g hg using f.domain_image
  refine ⟨⟨g, ?_⟩⟩
  intro r t ht
  obtain ⟨s,hs,he⟩ := f.tuple_image r t ht
  have same : g ∘ t = s := by
    funext i
    have hfirst := f.preserve (Edge.first (A := A) ⟨r,⟨t,ht⟩⟩ i)
    rw [he] at hfirst
    obtain ⟨j,hj⟩ := first_target hfirst
    have htag := f.tags (.port ⟨r,⟨t,ht⟩⟩ i)
    rw [hj] at htag
    have hij : j = i := by simpa [tag] using htag
    subst j
    have hsecond := f.preserve (Edge.second (A := A) ⟨r,⟨t,ht⟩⟩ i)
    rw [hj, hg (t i)] at hsecond
    exact Vertex.domain.inj (second_target hsecond)

  simpa [same] using hs

end TypedHom

theorem incidence_iff (A : Relational R arity V) (B : Relational R arity W) :
    Nonempty (TypedHom A B) ↔ Nonempty (Hom A B) := by
  constructor
  · rintro ⟨f⟩; exact f.recover
  · rintro ⟨f⟩; exact ⟨liftHom f⟩

/-- Incidence arcs strictly increase a three-layer rank. -/
def layer (A : Relational R arity V) : A.Vertex → ℕ
  | .tuple _ => 0
  | .port _ _ => 1
  | .domain _ => 2

theorem layer_increases (A : Relational R arity V) {u v} (h : A.Edge u v) :
    A.layer u < A.layer v := by cases h <;> simp [layer]

theorem edge_different_tags (A : Relational R arity V) {u v} (h : A.Edge u v) :
    A.tag u ≠ A.tag v := by cases h <;> simp [tag]

end Relational
end TreewidthHom
