module

public import TreewidthHom.OddCycleTarget

@[expose] public section

namespace TreewidthHom.OddCycle

/-- Within each block of length `t`, alternate between its two boundary colours. -/
def subdivisionProjection (t n : ℕ) (x : ZMod (t * n)) : ZMod n :=
  (x.val / t : ℕ) + ((x.val % t % 2 : ℕ) : ZMod n)

private theorem project_nat (t n x : ℕ) :
    subdivisionProjection t n (x : ZMod (t * n)) =
      ((x / t : ℕ) : ZMod n) + ((x % t % 2 : ℕ) : ZMod n) := by
  simp only [subdivisionProjection, ZMod.val_natCast, Nat.mod_mul_right_div_self,
    Nat.mod_mul_right_mod, ZMod.natCast_mod]

private theorem project_forward {t n d : ℕ} [NeZero n] (ht : Odd t) (hd : Odd d) (hle : d ≤ t)
    (x : ZMod (t * n)) :
    Near (subdivisionProjection t n x) (subdivisionProjection t n (x + d)) := by
  obtain ⟨k, hk⟩ := ht
  obtain ⟨j, hj⟩ := hd
  have hpos : 0 < t := by omega
  let _ : NeZero t := ⟨by omega⟩
  generalize hx : x.val = a
  have hcast : (a : ZMod (t * n)) = x := hx ▸ ZMod.natCast_zmod_val x
  rw [← hcast, ← Nat.cast_add, project_nat, project_nat]
  let r := a % t
  have hr : r < t := Nat.mod_lt _ hpos
  have hsum : a + d = r + d + t * (a / t) := by
    have := Nat.mod_add_div a t
    dsimp [r]
    omega
  rw [hsum, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  change Near _ (((((r + d) / t + a / t : ℕ) : ZMod n)) + (((r + d) % t % 2 : ℕ) : ZMod n))
  by_cases h : r + d < t
  · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, Nat.zero_add]
    change Near (((a / t : ℕ) : ZMod n) + ((r % 2 : ℕ) : ZMod n)) _
    rcases Nat.mod_two_eq_zero_or_one r with h₀ | h₁
    · exact Or.inl (by rw [h₀, show (r + d) % 2 = 1 by omega]; simp)
    · exact Or.inr (by rw [h₁, show (r + d) % 2 = 0 by omega]; simp)
  · have hsmall : r + d - t < t := by omega
    have he : r + d = (r + d - t) + t * 1 := by omega
    have hdiv : (r + d) / t = 1 := by
      conv_lhs => rw [he, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hsmall]
    have hmod : (r + d) % t = r + d - t := by
      conv_lhs => rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
    have hpar : (r + d - t) % 2 = r % 2 := by omega
    exact Or.inl (by rw [hdiv, hmod, hpar]; push_cast; ring)

/-- Projecting the endpoints of any length-`t` walk gives neighbours in the original
cycle. The lemma also works across the last block of the subdivided cycle. -/
theorem subdivisionProjection_walk {t n : ℕ} [NeZero n] (ht : Odd t)
    (W : ℕ → ZMod (t * n)) (hW : ∀ i < t, Near (W i) (W (i + 1))) :
    Near (subdivisionProjection t n (W 0)) (subdivisionProjection t n (W t)) := by
  obtain ⟨b, hb, he⟩ := walk_offset W t hW t le_rfl
  obtain ⟨k, hk⟩ := ht
  by_cases h : 2 * b ≤ t
  · have hd : Odd (t - 2 * b) := ⟨k - b, by omega⟩
    have he' : W t = W 0 + ((t - 2 * b : ℕ) : ZMod (t * n)) := by
      rw [he, Nat.cast_sub h]; push_cast; ring
    rw [he']
    exact project_forward ⟨k, hk⟩ hd (by omega) _
  · have hd : Odd (2 * b - t) := ⟨b - k - 1, by omega⟩
    have he' : W 0 = W t + ((2 * b - t : ℕ) : ZMod (t * n)) := by
      rw [he, Nat.cast_sub (by omega : t ≤ 2 * b)]; push_cast; ring
    apply Near.symm
    conv_rhs => rw [he']
    exact project_forward ⟨k, hk⟩ hd (by omega) _

end TreewidthHom.OddCycle
