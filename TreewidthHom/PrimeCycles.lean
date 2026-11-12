module

public import Mathlib

@[expose] public section

/-! # Directed cycle homomorphisms and prime marker separation -/
namespace TreewidthHom

/-- Edge-preservation between the directed successor cycles. -/
def CycleHom (p q : ℕ) (f : ZMod p → ZMod q) : Prop :=
  ∀ x, f (x + 1) = f x + 1

/-- Successor preservation forces the image of every natural-number position. -/
theorem cycleHom_nat (p q : ℕ) (f : ZMod p → ZMod q) (hf : CycleHom p q f) (n : ℕ) :
    f (n : ZMod p) = f 0 + (n : ZMod q) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [Nat.cast_add, ih, add_assoc] using hf (n : ZMod p)

/-- A homomorphism from a directed p-cycle to a directed q-cycle requires q | p. -/
theorem cycleHom_dvd (p q : ℕ) (f : ZMod p → ZMod q) (hf : CycleHom p q f) : q ∣ p := by
  have h := cycleHom_nat p q f hf p
  have hz : (p : ZMod q) = 0 := by
    simpa using (add_left_cancel (a := f 0) (by simpa using h.symm))
  exact (ZMod.natCast_eq_zero_iff p q).mp hz

/-- Distinct prime markers cannot map into one another. -/
theorem prime_cycleHom_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (f : ZMod p → ZMod q) (hf : CycleHom p q f) : p = q := by
  have hd := cycleHom_dvd p q f hf
  exact ((Nat.dvd_prime hp).mp hd).resolve_left hq.ne_one |>.symm

/-- An endomorphism of a nonempty finite directed cycle is a rotation. -/
theorem cycleHom_rotation (p : ℕ) [NeZero p] (f : ZMod p → ZMod p)
    (hf : CycleHom p p f) (x : ZMod p) : f x = f 0 + x := by
  simpa using cycleHom_nat p p f hf x.val

/-- The actual 18 marker lengths used in the reduction. -/
def markerPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]

theorem markerPrimes_length : markerPrimes.length = 18 := by decide

theorem markerPrimes_nodup : markerPrimes.Nodup := by decide

theorem markerPrimes_prime : ∀ p ∈ markerPrimes, p.Prime := by decide

end TreewidthHom
