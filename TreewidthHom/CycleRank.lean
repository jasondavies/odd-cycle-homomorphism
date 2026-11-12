module

public import TreewidthHom.PrimeCycles

@[expose] public section

namespace TreewidthHom

/-- A nondecreasing periodic natural-valued sequence is constant. -/
theorem monotone_periodic_constant (f : ℕ → ℕ) (p : ℕ) (hp : 0 < p)
    (hs : ∀ n, f n ≤ f (n+1)) (hperiod : ∀ n, f (n+p) = f n) :
    ∀ n, f n = f 0 := by
  have hm : Monotone f := monotone_nat_of_le_succ hs
  have hz : ∀ n, f (n*p) = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.succ_mul, hperiod] using ih
  intro n
  have hb : n ≤ n*p := Nat.le_mul_of_pos_right n hp
  exact le_antisymm ((hm hb).trans_eq (hz n)) (hm (Nat.zero_le n))

/-- A rank cannot strictly increase while going around a finite directed cycle. -/
theorem cycle_rank_constant (p : ℕ) [NeZero p] (r : ZMod p → ℕ)
    (hs : ∀ x, r x ≤ r (x+1)) : ∀ x, r x = r 0 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have h := monotone_periodic_constant (fun n => r (n : ZMod p)) p hp
    (by intro n; simpa using hs (n : ZMod p)) (by intro n; simp)
  intro x
  simpa using h x.val

end TreewidthHom
