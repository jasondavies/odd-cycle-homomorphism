module

public import Mathlib

@[expose] public section

/-!
# Attaching paths between chosen pairs of vertices

`linked B s t q` adds, for every link `l`, a new path with `q` internal vertices
between `s l` and `t l`. A homomorphism out of it is a homomorphism of the base
graph together with a walk of length `q+1` between the images of every link's ends.
-/
namespace TreewidthHom
open SimpleGraph

variable {V L : Type*}

def linked (B : SimpleGraph V) (s t : L → V) (q : ℕ) : SimpleGraph (V ⊕ (L × Fin q)) where
  Adj
    | .inl u, .inl v => B.Adj u v
    | .inl u, .inr (l,c) => (c.val = 0 ∧ u = s l) ∨ (c.val+1 = q ∧ u = t l)
    | .inr (l,c), .inl u => (c.val = 0 ∧ u = s l) ∨ (c.val+1 = q ∧ u = t l)
    | .inr (l,c), .inr (l',c') => l = l' ∧ (c'.val = c.val+1 ∨ c.val = c'.val+1)
  symm := ⟨by
    rintro (u | ⟨l,c⟩) (v | ⟨l',c'⟩) h
    · exact B.adj_symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by
    rintro (u | ⟨l,c⟩) h
    · exact B.loopless.irrefl u h
    · rcases h.2 with h | h <;> omega⟩

theorem linked_hom_iff {W : Type*} (H : SimpleGraph W) (B : SimpleGraph V) (s t : L → V)
    {q : ℕ} (hq : 0 < q) :
    Nonempty (linked B s t q →g H) ↔
      ∃ φ : B →g H, ∀ l, ∃ w : ℕ → W, w 0 = φ (s l) ∧ w (q+1) = φ (t l) ∧
        ∀ i ≤ q, H.Adj (w i) (w (i+1)) := by
  constructor
  · rintro ⟨ψ⟩
    refine ⟨⟨fun v => ψ (.inl v),fun h => ψ.map_rel (show (linked B s t q).Adj (.inl _) (.inl _) from h)⟩,
      fun l => ?_⟩
    refine ⟨fun i => if i = 0 then ψ (.inl (s l)) else
      if h : i ≤ q then ψ (.inr (l,⟨i-1,by omega⟩)) else ψ (.inl (t l)),?_,?_,?_⟩
    · simp
    · have h2 : ¬ q+1 ≤ q := by omega
      simp [h2]
    · intro i hi
      by_cases h0 : i = 0
      · subst h0
        have h1 : (0 : ℕ)+1 ≤ q := by omega
        simp only [↓reduceIte,Nat.add_eq_zero_iff,one_ne_zero,and_false,h1,↓reduceDIte]
        apply ψ.map_rel
        exact Or.inl ⟨rfl,rfl⟩
      · by_cases hlast : i = q
        · subst hlast
          have h1 : ¬ i+1 ≤ i := by omega
          simp only [h0,↓reduceIte,le_refl,↓reduceDIte,Nat.add_eq_zero_iff,one_ne_zero,
            and_false,h1]
          apply ψ.map_rel
          show (linked B s t i).Adj (.inr (l,⟨i-1,by omega⟩)) (.inl (t l))
          exact Or.inr ⟨by simp; omega,rfl⟩
        · have h1 : i ≤ q := hi
          have h2 : i+1 ≤ q := by omega
          simp only [h0,↓reduceIte,h1,↓reduceDIte,Nat.add_eq_zero_iff,one_ne_zero,and_false,h2]
          apply ψ.map_rel
          show (linked B s t q).Adj (.inr (l,⟨i-1,by omega⟩)) (.inr (l,⟨i+1-1,by omega⟩))
          exact ⟨rfl,Or.inl (by simp; omega)⟩
  · rintro ⟨φ,hw⟩
    choose w h0 hlast hstep using hw
    refine ⟨⟨fun x => match x with
      | .inl v => φ v
      | .inr (l,c) => w l (c.val+1),?_⟩⟩
    rintro (u | ⟨l,c⟩) (v | ⟨l',c'⟩) h
    · exact φ.map_rel h
    · rcases h with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
      · have := hstep l' 0 (by omega)
        rw [h0] at this
        simpa [hc] using this
      · have := (hstep l' q le_rfl).symm
        rw [hlast] at this
        simpa [hc] using this
    · rcases h with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
      · have := (hstep l 0 (by omega)).symm
        rw [h0] at this
        simpa [hc] using this
      · have := hstep l q le_rfl
        rw [hlast] at this
        simpa [hc] using this
    · obtain ⟨rfl,h | h⟩ := h
      · have := hstep l (c.val+1) (by have := c'.isLt; omega)
        simpa [h] using this
      · have := (hstep l (c'.val+1) (by have := c.isLt; omega)).symm
        simpa [h] using this

end TreewidthHom
