module

public import TreewidthHom.OddCycleTarget

@[expose] public section

/-! Reference cycles sharing an ordered edge. -/
namespace TreewidthHom.OddCycle.Reference
open SimpleGraph
variable {I : Type} {n : ℕ} [Fact (1 < n)]

/-- The two shared vertices, and the private vertices `2,...,n-1` of every copy. -/
abbrev RefVertex (I : Type) (n : ℕ) := Fin 2 ⊕ (I × Fin (n - 2))

/-- Vertex `d` of the reference cycle with index `s`. -/
def ref (s : I) (d : ZMod (n)) : RefVertex I n :=
  if h0 : d.val = 0 then .inl 0 else if h1 : d.val = 1 then .inl 1
  else .inr (s,⟨d.val-2,by have := ZMod.val_lt d; omega⟩)

/-- The coordinate of a reference vertex on its cycle. -/
def coord : RefVertex I n → ZMod (n)
  | .inl i => (i.val : ZMod (n))
  | .inr (_,e) => ((e.val+2 : ℕ) : ZMod (n))

@[simp] theorem ref_zero (s : I) : ref (n := n) s 0 = .inl 0 := by simp [ref]

@[simp] theorem ref_one (s : I) : ref (n := n) s 1 = .inl 1 := by
  simp [ref,ZMod.val_one]

theorem coord_ref (s : I) (d : ZMod (n)) : coord (ref s d) = d := by
  have hd := ZMod.natCast_zmod_val d
  unfold ref
  split_ifs with h0 h1
  · rw [h0] at hd
    simpa [coord] using hd
  · rw [h1] at hd
    simpa [coord] using hd
  · have : d.val-2+2 = d.val := by omega
    simp only [coord,this,hd]

/-- Reading the coordinate is a left inverse of each reference copy. -/
theorem ref_injective (s : I) : Function.Injective (ref (n := n) s) :=
  Function.LeftInverse.injective (coord_ref s)

theorem ref_ne (s : I) (d : ZMod (n)) : ref s d ≠ ref s (d+1) :=
  (ref_injective s).ne (fun h => one_ne_zero (left_eq_add.mp h))

theorem ref_private {s s' : I} {d : ZMod (n)}
    {e : Fin (n - 2)} (h : ref s d = .inr (s',e)) :
    s' = s ∧ d.val = e.val+2 := by
  unfold ref at h
  split_ifs at h with h0 h1
  have h2 := Sum.inr.inj h
  have h3 := congrArg (fun x : I × Fin (n - 2) => x.2.val) h2
  have h4 := congrArg (fun x : I × Fin (n - 2) => x.1) h2
  dsimp only at h3 h4
  exact ⟨h4.symm,by omega⟩

end TreewidthHom.OddCycle.Reference
