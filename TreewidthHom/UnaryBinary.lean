module

public import TreewidthHom.Schema

@[expose] public section

namespace TreewidthHom

/-- The fixed schema: one unary root relation and five binary relations. -/
structure UnaryBinary (V : Type*) where
  root : V → Prop
  binary : Fin 5 → V → V → Prop

namespace UnaryBinary
variable {V W : Type*}

structure Hom (A : UnaryBinary V) (B : UnaryBinary W) where
  map : V → W
  root : ∀ v, A.root v → B.root (map v)
  binary : ∀ r u v, A.binary r u v → B.binary r (map u) (map v)

def asRelational (A : UnaryBinary V) : Relational (Fin 6) Relational.schemaArity V where
  holds r t := if h : r = 0 then
    A.root (t ⟨0,by simp [Relational.schemaArity,h]⟩)
  else
    A.binary ⟨r.val-1,by have := r.isLt; omega⟩
      (t ⟨0,by simp [Relational.schemaArity,h]⟩)
      (t ⟨1,by simp [Relational.schemaArity,h]⟩)

def pairTuple (r : Fin 5) (u v : V) : Fin (Relational.schemaArity r.succ) → V :=
  fun j => if j.val = 0 then u else v

@[simp] theorem holds_root (A : UnaryBinary V) (v : V) :
    A.asRelational.holds 0 (fun _ => v) ↔ A.root v := by simp [asRelational]

@[simp] theorem holds_binary (A : UnaryBinary V) (r : Fin 5) (u v : V) :
    A.asRelational.holds r.succ (pairTuple r u v) ↔ A.binary r u v := by
  simp [asRelational, pairTuple, Fin.succ_ne_zero]

@[simp] theorem comp_pair (f : V → W) (r : Fin 5) (u v : V) :
    f ∘ pairTuple r u v = pairTuple r (f u) (f v) := by
  funext j
  simp only [Function.comp_apply,pairTuple]
  split <;> rfl

def Hom.toRelational {A : UnaryBinary V} {B : UnaryBinary W} (f : Hom A B) :
    Relational.Hom A.asRelational B.asRelational where
  map := f.map
  preserve := by
    intro r t h
    unfold asRelational at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with hr
    · exact f.root _ h
    · exact f.binary _ _ _ h

def fromRelational {A : UnaryBinary V} {B : UnaryBinary W}
    (f : Relational.Hom A.asRelational B.asRelational) : Hom A B where
  map := f.map
  root := by
    intro v hv
    simpa [Function.comp_def] using f.preserve 0 (fun _ => v) ((holds_root A v).mpr hv)
  binary := by
    intro r u v h
    simpa using f.preserve r.succ (pairTuple r u v) ((holds_binary A r u v).mpr h)

theorem hom_iff_relational (A : UnaryBinary V) (B : UnaryBinary W) :
    Nonempty (Hom A B) ↔ Nonempty (Relational.Hom A.asRelational B.asRelational) :=
  ⟨fun ⟨f⟩ => ⟨f.toRelational⟩, fun ⟨f⟩ => ⟨fromRelational f⟩⟩

end UnaryBinary
end TreewidthHom
