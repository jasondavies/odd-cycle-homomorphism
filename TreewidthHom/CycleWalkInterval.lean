module

public import TreewidthHom.OddCycleTarget

@[expose] public section

namespace TreewidthHom.OddCycle

/-- After multiplication by the inverse of two, the reachable endpoints of a walk
of length `L` form a cyclic interval of `L+1` consecutive residues. -/
theorem walk_iff_interval {n : ℕ} (hn : Odd n) (L : ℕ) (x y : ZMod n) :
    (∃ W : ℕ → ZMod n, W 0 = x ∧ W L = y ∧ ∀ i < L, Near (W i) (W (i + 1))) ↔
      ∃ j ≤ L, (((n / 2 + 1 : ℕ) : ZMod n) * (y - x)) =
        -(((n / 2 + 1 : ℕ) : ZMod n) * L) + j := by
  let c : ZMod n := (n / 2 + 1 : ℕ)
  change _ ↔ ∃ j ≤ L, c * (y - x) = -(c * L) + j
  have hc : 2 * c = 1 := by
    obtain ⟨k, hk⟩ := hn
    have h : 2 * (n / 2 + 1) = n + 1 := by omega
    have h' := congrArg (fun m : ℕ => (m : ZMod n)) h
    simpa [c, Nat.cast_add, Nat.cast_mul] using h'
  constructor
  · rintro ⟨W, hx, hy, hW⟩
    obtain ⟨b, hb, he⟩ := walk_offset W L hW L le_rfl
    rw [hx, hy] at he
    refine ⟨L - b, by omega, ?_⟩
    rw [he, Nat.cast_sub hb]
    linear_combination ((L : ZMod n) - b) * hc
  · rintro ⟨j, hj, he⟩
    have hxy : y = x + 2 * j - L := by
      linear_combination 2 * he - (y - x + L) * hc
    by_cases h : L ≤ 2 * j
    · apply walk_of_offset x y 1 (Or.inl rfl) (2 * j - L) L (by omega) (by omega)
      rw [Nat.cast_sub h, hxy]; push_cast; ring
    · apply walk_of_offset x y (-1) (Or.inr rfl) (L - 2 * j) L (by omega) (by omega)
      rw [Nat.cast_sub (by omega : 2 * j ≤ L), hxy]; push_cast; ring

end TreewidthHom.OddCycle
