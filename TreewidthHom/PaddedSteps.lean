module

public import Mathlib

@[expose] public section

/-! # Fixed-length stuttering paths followed by a strict advance -/
namespace TreewidthHom

/-- A transition on a string position may stay put or advance by one. -/
def Step (a b : ℕ) : Prop := b = a ∨ b = a + 1

/-- N Step edges and one final Advance edge, the block used in the LCS query. -/
def PaddedAdvance (N a b : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, f 0 = a ∧ f (N + 1) = b ∧
    (∀ j < N, Step (f j) (f (j + 1))) ∧ f (N + 1) = f N + 1

theorem step_bounds {a b : ℕ} (h : Step a b) : a ≤ b ∧ b ≤ a + 1 := by
  rcases h with rfl | rfl <;> omega

/-- Every legal prefix stays between its starting position and its length bound. -/
theorem trace_bounds {N a : ℕ} {f : ℕ → ℕ} (hstart : f 0 = a)
    (hsteps : ∀ j < N, Step (f j) (f (j + 1))) {j : ℕ} (hj : j ≤ N) :
    a ≤ f j ∧ f j ≤ a + j := by
  induction j with
  | zero => simp [hstart]
  | succ j ih =>
    have hb := ih (by omega)
    have hs := step_bounds (hsteps j (by omega))
    omega

/-- The precise expressive power of a padded block. -/
theorem paddedAdvance_iff {N a b : ℕ} :
    PaddedAdvance N a b ↔ a < b ∧ b ≤ a + N + 1 := by
  constructor
  · rintro ⟨f, h0, hlast, hsteps, hfinal⟩
    have hb := trace_bounds h0 hsteps (Nat.le_refl N)
    omega
  · rintro ⟨hlt, hle⟩
    let d := b - a - 1
    have hd : d ≤ N := by dsimp [d]; omega
    have hb : a + d + 1 = b := by dsimp [d]; omega
    let f := fun j => if j ≤ N then a + min j d else b
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · simp [f]
    · simp [f]
    · intro j hj
      dsimp [f]
      rw [ite_eq_left (by omega : j ≤ N), ite_eq_left (by omega : j + 1 ≤ N)]
      unfold Step
      omega
    · simp [f, Nat.min_eq_right hd, hb]

/-- N as a global string-length bound allows every strictly increasing choice. -/
theorem paddedAdvance_iff_lt {N a b : ℕ} (hb : b ≤ N) :
    PaddedAdvance N a b ↔ a < b := by
  rw [paddedAdvance_iff]
  omega

/-- Padded blocks cannot skip backwards or select the same occurrence twice. -/
theorem paddedAdvance_strict {N a b : ℕ} (h : PaddedAdvance N a b) : a < b :=
  paddedAdvance_iff.mp h |>.1

end TreewidthHom
