module

public import TreewidthHom.OddCycleTarget

@[expose] public section

/-!
# Capping the target length

A homomorphism to a cycle that misses a vertex yields a bipartition: cut the
cycle at that vertex and use parity along the remaining path. Consequently,
targets larger than the source order can be replaced by any other such target.
-/

namespace TreewidthHom.OddCycle
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [Fact (1 < n)]

theorem hom_of_bipartite (h : G.IsBipartite) : Nonempty (G →g cyc n) := by
  obtain ⟨c⟩ := h
  refine ⟨{ toFun := fun v => if c v = 0 then 0 else 1, map_rel' := ?_ }⟩
  intro u v huv
  have hc := c.valid huv
  have cases (x : Fin 2) : x = 0 ∨ x = 1 := by
    have := x.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases (c u) with hu | hu <;> rcases cases (c v) with hv | hv
  · exact (hc (hu.trans hv.symm)).elim
  · simp [hu, hv]
  · simp [hu, hv]
  · exact (hc (hu.trans hv.symm)).elim

private theorem parity_ne_of_near {a b : ZMod n} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Near a b) : a.val % 2 ≠ b.val % 2 := by
  have hn : 1 < n := Fact.out
  have hstep : ∀ x y : ZMod n, y ≠ 0 → y = x + 1 → y.val = x.val + 1 := by
    intro x y hy he
    have hx := ZMod.val_lt x
    have hv : y.val = (x.val + 1) % n := by rw [he, ZMod.val_add, ZMod.val_one]
    have hsmall : x.val + 1 < n := by
      by_contra hnot
      have heq : x.val + 1 = n := by omega
      have : y.val = 0 := by simp [hv, heq]
      exact hy (ZMod.val_injective n (by simpa using this))
    rw [Nat.mod_eq_of_lt hsmall] at hv
    exact hv
  rcases h with h | h
  · have := hstep a b hb h
    omega
  · have := hstep b a ha h
    omega

/-- Cutting the target cycle at an unused vertex gives a two-colouring. -/
theorem bipartite_of_hom_misses (f : G →g cyc n) (r : ZMod n)
    (hr : ∀ v, f v ≠ r) : G.IsBipartite := by
  let c : V → Fin 2 := fun v => ⟨(f v - r).val % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨Coloring.mk c ?_⟩
  intro u v huv he
  have hnear := (cyc_adj _ _).mp (f.map_adj huv)
  have hshift : Near (f u - r) (f v - r) := by
    rcases hnear with h | h
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (by rw [h]; ring)
  exact parity_ne_of_near (sub_ne_zero.mpr (hr u)) (sub_ne_zero.mpr (hr v))
    hshift (congrArg Fin.val he)

/-- A cycle longer than the source order receives a homomorphism exactly from
bipartite graphs. No parity assumption on the target is needed here. -/
theorem hom_iff_bipartite_of_card_lt [Fintype V] (hn : Fintype.card V < n) :
    Nonempty (G →g cyc n) ↔ G.IsBipartite := by
  constructor
  · rintro ⟨f⟩
    have hnot : ¬ Function.Surjective f := by
      intro hs
      have := Fintype.card_le_of_surjective f hs
      simp only [ZMod.card] at this
      omega
    simp only [Function.Surjective, not_forall, not_exists] at hnot
    obtain ⟨r, hr⟩ := hnot
    exact bipartite_of_hom_misses f r hr
  · exact hom_of_bipartite

/-- The cap used by the binary-input algorithm preserves ordinary homomorphism. -/
theorem hom_iff_capped [Fintype V] (_hn : 5 ≤ n) :
    Nonempty (G →g cyc n) ↔ Nonempty (G →g cyc (min n (2 * Fintype.card V + 5))) := by
  by_cases hsmall : n ≤ 2 * Fintype.card V + 5
  · rw [min_eq_left hsmall]
  · rw [min_eq_right (by omega : 2 * Fintype.card V + 5 ≤ n)]
    let : Fact (1 < 2 * Fintype.card V + 5) := ⟨by omega⟩
    rw [hom_iff_bipartite_of_card_lt (by omega : Fintype.card V < n),
      hom_iff_bipartite_of_card_lt (by omega : Fintype.card V < 2 * Fintype.card V + 5)]

omit [Fact (1 < n)] in
/-- Capping retains the odd target convention and makes its order linear in
the source order. The statement is purely mathematical, not a transducer bound. -/
theorem capped_length_spec (m : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    5 ≤ min n (2 * m + 5) ∧ Odd (min n (2 * m + 5)) ∧
    min n (2 * m + 5) ≤ 2 * m + 5 := by
  refine ⟨by omega, ?_, min_le_right _ _⟩
  rcases le_total n (2 * m + 5) with h | h
  · simpa only [min_eq_left h] using hodd
  · rw [min_eq_right h]
    exact ⟨m + 2, by omega⟩

end TreewidthHom.OddCycle
