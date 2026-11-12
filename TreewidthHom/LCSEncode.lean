module

public import TreewidthHom.LCSInstance

@[expose] public section

namespace TreewidthHom.LCSInstance
namespace Encode
variable {k N ℓ : ℕ} {words : Fin k → List Bool}
variable (e : ∀ i, Fin ℓ ↪o Fin (words i).length)

/-- Sentinel zero followed by the chosen, one-based occurrences. -/
def selected (i : Fin k) (j : Fin (ℓ+1)) : ℕ :=
  if h : j.val = 0 then 0 else (e i ⟨j.val-1,by have := j.isLt; omega⟩).val+1

@[simp] theorem selected_zero (i : Fin k) : selected e i 0 = 0 := by simp [selected]
@[simp] theorem selected_succ (i : Fin k) (j : Fin ℓ) :
    selected e i j.succ = (e i j).val+1 := by simp [selected]

theorem selected_bound (i : Fin k) (j : Fin (ℓ+1)) : selected e i j ≤ (words i).length := by
  unfold selected
  split
  · omega
  · have h := (e i ⟨j.val-1,by have := j.isLt; omega⟩).isLt
    omega

theorem selected_strict (i : Fin k) (j : Fin ℓ) :
    selected e i j.castSucc < selected e i j.succ := by
  rw [selected_succ]
  unfold selected
  split
  · omega
  · rename_i h
    have hj : (⟨j.castSucc.val-1,by have := j.isLt; omega⟩ : Fin ℓ) < j := by
      change j.val-1 < j.val
      have := j.isLt
      simp only [Fin.val_castSucc] at h
      omega
    have he := (e i).strictMono hj
    exact Nat.add_lt_add_right he 1

def trace (i : Fin k) (j : Fin ℓ) (s : Fin (N+1)) : ℕ :=
  selected e i j.castSucc + min s.val (selected e i j.succ - selected e i j.castSucc - 1)

@[simp] theorem trace_zero (i : Fin k) (j : Fin ℓ) :
    trace (N := N) e i j 0 = selected e i j.castSucc := by simp [trace]

theorem trace_bound (i : Fin k) (j : Fin ℓ) (s : Fin (N+1)) : trace e i j s ≤ (words i).length := by
  have hs := selected_strict e i j
  have hb := selected_bound e i j.succ
  unfold trace
  omega

theorem trace_step (i : Fin k) (j : Fin ℓ) (s : Fin N) :
    Step (trace e i j s.castSucc) (trace e i j s.succ) := by
  unfold trace Step
  simp only [Fin.val_castSucc,Fin.val_succ]
  omega

theorem trace_advance (hN : ∀ i, (words i).length ≤ N) (i : Fin k) (j : Fin ℓ) :
    selected e i j.succ = trace e i j (Fin.last N) + 1 := by
  have hs := selected_strict e i j
  have hb := selected_bound e i j.succ
  have hn := hN i
  unfold trace
  simp only [Fin.val_last]
  omega

def coordinate (i : Fin k) : Position N ℓ → Fin ((words i).length+1)
  | .inl (j,s) => ⟨trace e i j s,by have := trace_bound e i j s; omega⟩
  | .inr _ => ⟨selected e i (Fin.last ℓ),by have := selected_bound e i (Fin.last ℓ); omega⟩

theorem coordinate_boundary (i : Fin k) (j : Fin (ℓ+1)) :
    (coordinate (N := N) e i (boundary j)).val = selected e i j := by
  by_cases hj : j.val < ℓ
  · have he : (⟨j.val,hj⟩ : Fin ℓ).castSucc = j := by ext; rfl
    simp only [boundary, dite_eq_left hj, coordinate, trace_zero, he]
  · have he : j = Fin.last ℓ := by ext; have := j.isLt; simp; omega
    subst j
    simp [coordinate]

variable (z : Fin ℓ → Bool)

def vertexMap : QueryVertex k N ℓ → TargetVertex words
  | .anchor i => .anchor i
  | .row i p => .pos i (coordinate e i p)
  | .letter j => .bit (z j)

/-- A common subsequence supplies a homomorphism of the complete concrete structures. -/
def hom (hN : ∀ i, (words i).length ≤ N)
    (hz : ∀ i j, z j = (words i).get (e i j)) :
    UnaryBinary.Hom (query k N ℓ) (target words) where
  map := vertexMap e z
  root := by intro v hv; change v = .anchor 0 at hv; subst v; rfl
  binary := by
    intro r u v h
    cases h with
    | next i => exact .next i
    | begin i =>
      change TargetEdge words 1 (.anchor i.succ) (.pos i (coordinate e i (boundary 0)))
      have he : coordinate (N := N) e i (boundary 0) = 0 := by
        apply Fin.ext
        simp [coordinate_boundary]
      rw [he]
      exact .begin i
    | step i j s => exact .step i _ _ (trace_step e i j s)
    | advance i j =>
      apply TargetEdge.advance i
      rw [coordinate_boundary]
      exact trace_advance e hN i j
    | letter i j =>
      change TargetEdge words 4 (.pos i (coordinate e i (boundary j.succ))) (.bit (z j))
      have he : coordinate (N := N) e i (boundary j.succ) = occurrence i (e i j) := by
        apply Fin.ext
        simp [coordinate_boundary,occurrence]
      rw [he,hz i j]
      exact .letter i (e i j)

end Encode

/-- Forward correctness for every length, including the empty subsequence. -/
theorem commonSubsequence_hom {k N ℓ : ℕ} {words : Fin k → List Bool}
    (hN : ∀ i, (words i).length ≤ N) (h : CommonSubsequence words ℓ) :
    Nonempty (UnaryBinary.Hom (query k N ℓ) (target words)) := by
  obtain ⟨z,hz⟩ := (commonSubsequence_iff_embedding words ℓ).mp h
  choose e he using hz
  exact ⟨Encode.hom e z hN he⟩

end TreewidthHom.LCSInstance
