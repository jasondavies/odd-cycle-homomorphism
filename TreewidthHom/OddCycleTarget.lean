module

public import Mathlib

@[expose] public section

/-!
# Homomorphisms and walks into an odd cycle

The cycle on `ZMod n` is mathlib's circulant graph with jump set `{1}`.
For odd `n`, a map of the cycle to itself is a rotation or a reflection, and two
residues are joined by a walk of length `n-2` exactly when they differ.
-/
namespace TreewidthHom.OddCycle
open SimpleGraph

variable {n : ℕ}

/-- Consecutive residues. -/
def Near (u v : ZMod n) : Prop := v = u + 1 ∨ u = v + 1

theorem Near.symm {u v : ZMod n} (h : Near u v) : Near v u := h.elim Or.inr Or.inl

/-- The cycle on the residues modulo `n`. -/
abbrev cyc (n : ℕ) : SimpleGraph (ZMod n) := circulantGraph {1}

theorem cyc_adj [Fact (1 < n)] (u v : ZMod n) : (cyc n).Adj u v ↔ Near u v := by
  simp only [circulantGraph_adj,Set.mem_singleton_iff,Near]
  constructor
  · rintro ⟨_,h | h⟩
    · exact Or.inr (sub_eq_iff_eq_add'.mp h)
    · exact Or.inl (sub_eq_iff_eq_add'.mp h)
  · intro h
    have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero
    rcases h with h | h
    · refine ⟨fun he => h1 ?_,Or.inr (by rw [h]; ring)⟩
      rw [he] at h
      exact (left_eq_add.mp h)
    · refine ⟨fun he => h1 ?_,Or.inl (by rw [h]; ring)⟩
      rw [← he] at h
      exact (left_eq_add.mp h)

/-- The cycle of length `m+1` is mathlib's cycle graph. -/
theorem cyc_eq_cycleGraph (m : ℕ) : cyc (m+1) = cycleGraph (m+1) :=
  (cycleGraph_eq_circulantGraph m).symm

/-- Successor coordinates do not wrap when the successor is nonzero. -/
theorem val_succ_of_ne_zero {n : ℕ} [Fact (1 < n)] {a b : ZMod n} (hb : b ≠ 0)
    (h : b = a + 1) : b.val = a.val + 1 := by
  have hn : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  have hval : b.val = (a.val+1) % n := by rw [h,ZMod.val_add,ZMod.val_one]
  have hlt := ZMod.val_lt a
  rcases Nat.lt_or_ge (a.val+1) n with h1 | h1
  · rwa [Nat.mod_eq_of_lt h1] at hval
  · have h2 : a.val+1 = n := by omega
    rw [h2,Nat.mod_self] at hval
    exact absurd ((ZMod.val_eq_zero b).mp hval) hb


/-! ## A cycle maps to itself by a rotation or a reflection -/

theorem natCast_two_mul_eq_zero (hodd : Odd n) {b : ℕ} (h : ((2*b : ℕ) : ZMod n) = 0) :
    n ∣ b := by
  have hd : n ∣ 2*b := (ZMod.natCast_eq_zero_iff _ _).mp h
  have hc : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hodd
  exact hc.dvd_of_dvd_mul_left hd

/-- A map that moves by one step at a time around an odd cycle never turns. -/
theorem rotation_or_reflection [Fact (1 < n)] (hodd : Odd n) (f : ZMod n → ZMod n)
    (hf : ∀ x, Near (f x) (f (x+1))) :
    ∃ r ε : ZMod n, (ε = 1 ∨ ε = -1) ∧ ∀ x, f x = r + ε*x := by
  classical
  have hn : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  -- every step is forward or backward, never both
  let fwd : ZMod n → Prop := fun x => f (x+1) = f x + 1
  have hstep : ∀ x, f (x+1) - f x = if fwd x then 1 else -1 := by
    intro x
    by_cases hx : fwd x
    · rw [ite_eq_left hx,hx]; ring
    · rw [ite_eq_right hx]
      rcases hf x with h | h
      · exact absurd h hx
      · rw [h]; ring
  have hsum : ∑ x : ZMod n, (f (x+1) - f x) = 0 := by
    rw [Finset.sum_sub_distrib]
    have he : ∑ x : ZMod n, f (x+1) = ∑ x : ZMod n, f x :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) f
    rw [he,sub_self]
  let F := (Finset.univ.filter fwd).card
  let Bk := (Finset.univ.filter (fun x => ¬ fwd x)).card
  have hFB : F + Bk = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod n))) fwd
    simpa [F,Bk,ZMod.card] using h
  have hcount : (F : ZMod n) - (Bk : ZMod n) = 0 := by
    rw [← hsum]
    have hs : ∑ x : ZMod n, (f (x+1) - f x) = ∑ x : ZMod n, (if fwd x then (1 : ZMod n) else -1) :=
      Finset.sum_congr rfl (fun x _ => hstep x)
    rw [hs,Finset.sum_ite,Finset.sum_const,Finset.sum_const]
    simp only [nsmul_eq_mul,mul_one,mul_neg,F,Bk]
    ring
  have hB : n ∣ Bk := by
    apply natCast_two_mul_eq_zero hodd
    have hF : (F : ZMod n) = -(Bk : ZMod n) := by
      have h : ((F + Bk : ℕ) : ZMod n) = 0 := by rw [hFB]; exact ZMod.natCast_self n
      push_cast at h
      exact eq_neg_of_add_eq_zero_left h
    rw [hF] at hcount
    push_cast
    have : (2 : ZMod n) * Bk = -(-(Bk : ZMod n) - Bk) := by ring
    rw [this,hcount,neg_zero]
  have hcases : Bk = 0 ∨ Bk = n := by
    rcases Nat.eq_zero_or_pos Bk with h | h
    · exact Or.inl h
    · right
      have := Nat.le_of_dvd h hB
      omega
  rcases hcases with h0 | hfull
  · -- all steps forward
    have hall : ∀ x, f (x+1) = f x + 1 := by
      intro x
      by_contra hx
      have : x ∈ Finset.univ.filter (fun x => ¬ fwd x) := by simp [fwd,hx]
      have hpos := Finset.card_pos.mpr ⟨x,this⟩
      omega
    refine ⟨f 0,1,Or.inl rfl,fun x => ?_⟩
    have hnat : ∀ m : ℕ, f (m : ZMod n) = f 0 + m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => push_cast; rw [hall,ih]; ring
    have := hnat x.val
    rw [ZMod.natCast_zmod_val] at this
    rw [this]; ring
  · -- all steps backward
    have hall : ∀ x, f (x+1) = f x - 1 := by
      intro x
      have hx : ¬ fwd x := by
        by_contra hx
        have : x ∈ Finset.univ.filter fwd := by simp [hx]
        have hpos := Finset.card_pos.mpr ⟨x,this⟩
        omega
      rcases hf x with h | h
      · exact absurd h hx
      · rw [h]; ring
    refine ⟨f 0,-1,Or.inr rfl,fun x => ?_⟩
    have hnat : ∀ m : ℕ, f (m : ZMod n) = f 0 - m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => push_cast; rw [hall,ih]; ring
    have := hnat x.val
    rw [ZMod.natCast_zmod_val] at this
    rw [this]; ring

/-! ## Difference paths: walks of length `n-2` join exactly the distinct residues -/

/-- A walk of `t` steps has moved by `t` minus twice its number of backward steps. -/
theorem walk_offset (W : ℕ → ZMod n) (T : ℕ) (hW : ∀ t < T, Near (W t) (W (t+1))) :
    ∀ t ≤ T, ∃ b ≤ t, W t = W 0 + t - 2*b := by
  intro t
  induction t with
  | zero => intro _; exact ⟨0,le_rfl,by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨b,hb,he⟩ := ih (by omega)
    rcases hW t (by omega) with h | h
    · exact ⟨b,by omega,by rw [h,he]; push_cast; ring⟩
    · refine ⟨b+1,by omega,?_⟩
      have h' : W (t+1) = W t - 1 := by rw [h]; ring
      rw [h',he]; push_cast; ring

/-- An odd closed walk around a cycle must traverse at least its length. -/
theorem odd_closed_walk_length (W : ℕ → ZMod n) (T : ℕ) (hodd : Odd T)
    (hclosed : W T = W 0) (hW : ∀ t < T, Near (W t) (W (t+1))) : n ≤ T := by
  by_contra hn
  have hT : T < n := by omega
  obtain ⟨b,hb,he⟩ := walk_offset W T hW T le_rfl
  have heq : (T : ZMod n) = ((2*b : ℕ) : ZMod n) := by
    rw [hclosed] at he
    push_cast
    linear_combination -he
  have small_zero : ∀ d : ℕ, d < n → (d : ZMod n) = 0 → d = 0 := by
    intro d hd hz
    have hdiv := (ZMod.natCast_eq_zero_iff d n).mp hz
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    rwa [Nat.mod_eq_of_lt hd] at hmod
  rcases le_total (2*b) T with h | h
  · have hz : T-2*b = 0 := small_zero _ (by omega) (by
      rw [Nat.cast_sub h,heq,sub_self])
    obtain ⟨a,ha⟩ := hodd
    omega
  · have hz : 2*b-T = 0 := small_zero _ (by omega) (by
      rw [Nat.cast_sub h,← heq,sub_self])
    obtain ⟨a,ha⟩ := hodd
    omega

/-- A homomorphism from an odd cycle cannot increase its length. -/
theorem length_le_of_hom {k : ℕ} [Fact (1 < k)] [Fact (1 < n)]
    (hk : Odd k) (f : cyc k →g cyc n) : n ≤ k := by
  apply odd_closed_walk_length (fun t => f (t : ZMod k)) k hk
  · simp
  · intro t _
    apply (cyc_adj _ _).mp
    apply f.map_adj
    apply (cyc_adj _ _).mpr
    exact Or.inl (by push_cast; rfl)

/-- Homomorphically equivalent odd cycles have the same length. -/
theorem length_eq_of_homs {k : ℕ} [Fact (1 < k)] [Fact (1 < n)]
    (hk : Odd k) (hn : Odd n) (f : cyc k →g cyc n) (g : cyc n →g cyc k) : k = n :=
  Nat.le_antisymm (length_le_of_hom hn g) (length_le_of_hom hk f)

theorem walk_ne (hodd : Odd n) (hn : 3 ≤ n) (W : ℕ → ZMod n)
    (hW : ∀ t < n-2, Near (W t) (W (t+1))) : W 0 ≠ W (n-2) := by
  obtain ⟨b,hb,he⟩ := walk_offset W (n-2) hW (n-2) le_rfl
  intro h
  rw [he] at h
  have hz : ((2*(b+1) : ℕ) : ZMod n) = 0 := by
    have hcast : ((n-2 : ℕ) : ZMod n) = -2 := by
      rw [Nat.cast_sub (by omega),ZMod.natCast_self]; simp
    rw [hcast] at h
    push_cast
    have h3 : (0 : ZMod n) = -2 - 2*(b : ZMod n) := by
      have := sub_eq_zero.mpr h.symm
      rw [← this]; ring
    rw [show (2 : ZMod n)*((b : ZMod n)+1) = -(-2 - 2*(b : ZMod n)) by ring,← h3,neg_zero]
  have hd := natCast_two_mul_eq_zero hodd hz
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- A stuttering walk: `e` steps in one direction, then back and forth. -/
theorem walk_of_offset (u v σ : ZMod n) (hσ : σ = 1 ∨ σ = -1) (e T : ℕ) (he : e ≤ T)
    (hpar : (T - e) % 2 = 0) (hv : v = u + σ*e) :
    ∃ W : ℕ → ZMod n, W 0 = u ∧ W T = v ∧ ∀ t < T, Near (W t) (W (t+1)) := by
  refine ⟨fun t => if t ≤ e then u + σ*t else v + ((t-e) % 2 : ℕ),?_,?_,?_⟩
  · simp
  · by_cases h : T ≤ e
    · have : T = e := by omega
      simp [this,hv]
    · simp [h,hpar]
  · intro t _
    dsimp only
    by_cases h1 : t+1 ≤ e
    · rw [ite_eq_left (by omega : t ≤ e),ite_eq_left h1]
      push_cast
      rcases hσ with rfl | rfl
      · exact Or.inl (by ring)
      · exact Or.inr (by ring)
    · by_cases h2 : t ≤ e
      · have ht : t = e := by omega
        rw [ite_eq_left h2,ite_eq_right h1,ht,← hv]
        have : (e+1-e) % 2 = 1 := by omega
        rw [this]
        exact Or.inl (by simp)
      · rw [ite_eq_right h2,ite_eq_right h1]
        rcases Nat.mod_two_eq_zero_or_one (t-e) with h | h
        · have h' : (t+1-e) % 2 = 1 := by omega
          rw [h,h']
          exact Or.inl (by simp)
        · have h' : (t+1-e) % 2 = 0 := by omega
          rw [h,h']
          exact Or.inr (by simp)

/-- Two residues of an odd cycle are joined by a walk of length `n-2` if and only
if they are different. -/
theorem walk_iff_ne (hodd : Odd n) (hn : 3 ≤ n) (u v : ZMod n) :
    (∃ W : ℕ → ZMod n, W 0 = u ∧ W (n-2) = v ∧ ∀ t < n-2, Near (W t) (W (t+1))) ↔ u ≠ v := by
  have hne : NeZero n := ⟨by omega⟩
  constructor
  · rintro ⟨W,rfl,rfl,hW⟩
    exact walk_ne hodd hn W hW
  · intro huv
    let d := (v - u).val
    have hd0 : d ≠ 0 := by
      intro h
      exact huv ((sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h)).symm)
    have hdn : d < n := ZMod.val_lt _
    have hdv : v = u + (d : ZMod n) := by
      rw [ZMod.natCast_zmod_val]; ring
    obtain ⟨m,hm⟩ := hodd
    rcases Nat.mod_two_eq_zero_or_one d with hpar | hpar
    · -- even offset: go backward by n-d
      apply walk_of_offset u v (-1) (Or.inr rfl) (n-d) (n-2) (by omega) (by omega)
      rw [hdv,Nat.cast_sub hdn.le,ZMod.natCast_self]; ring
    · -- odd offset: go forward by d
      apply walk_of_offset u v 1 (Or.inl rfl) d (n-2) (by omega) (by omega)
      rw [hdv]; ring

end TreewidthHom.OddCycle
