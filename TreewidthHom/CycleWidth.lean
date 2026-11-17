module

public import TreewidthHom.OddCycleTarget
public import TreewidthHom.PathWidth

@[expose] public section

/-! The odd cycle has a supplied path decomposition of width two. -/
namespace TreewidthHom.OddCycle
open SimpleGraph

/-- A cycle of length at least three has pathwidth at most two: keep vertex 0 and
slide a window of two consecutive vertices. -/
theorem target_pathWidth (n : ℕ) [Fact (1 < n)] (hn : 3 ≤ n) : HasPathWidth (cyc n) 2 := by
  classical
  have hne : NeZero n := ⟨by omega⟩
  let bag : Fin (n-3+1) → Finset (ZMod n) := fun τ =>
    Finset.univ.filter (fun a => a = 0 ∨ a.val = τ.val+1 ∨ a.val = τ.val+2)
  have hmem : ∀ a τ, a ∈ bag τ ↔ (a = 0 ∨ a.val = τ.val+1 ∨ a.val = τ.val+2) := by
    intro a τ
    simp [bag]
  let D : Decomposition (cyc n) (pathGraph (n-3+1)) :=
    intervalDecomposition (cyc n) (n-3) bag
      (by
        intro a
        have hlt := ZMod.val_lt a
        by_cases h0 : a = 0
        · exact ⟨0,(hmem a 0).mpr (Or.inl h0)⟩
        · have h1 : a.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero a).mp h)
          by_cases h2 : a.val = n-1
          · exact ⟨⟨n-3,by omega⟩,(hmem a _).mpr (Or.inr (Or.inr (by simp; omega)))⟩
          · exact ⟨⟨a.val-1,by omega⟩,(hmem a _).mpr (Or.inr (Or.inl (by simp; omega)))⟩)
      (by
        have key : ∀ a b : ZMod n, b = a + 1 → ∃ τ, a ∈ bag τ ∧ b ∈ bag τ := by
          intro a b hab
          have hlta := ZMod.val_lt a
          have hltb := ZMod.val_lt b
          by_cases ha : a = 0
          · have hb1 : b.val = 1 := by rw [hab,ha,zero_add,ZMod.val_one]
            exact ⟨⟨0,by omega⟩,(hmem a _).mpr (Or.inl ha),(hmem b _).mpr (Or.inr (Or.inl (by simp [hb1])))⟩
          · have ha1 : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
            by_cases hb : b = 0
            · have hval : (a.val+1) % n = 0 := by
                have := congrArg ZMod.val hab
                rw [hb,ZMod.val_zero,ZMod.val_add,ZMod.val_one] at this
                exact this.symm
              have han : a.val = n-1 := by
                rcases Nat.lt_or_ge (a.val+1) n with h1 | h1
                · rw [Nat.mod_eq_of_lt h1] at hval; omega
                · omega
              exact ⟨⟨n-3,by omega⟩,(hmem a _).mpr (Or.inr (Or.inr (by simp; omega))),
                (hmem b _).mpr (Or.inl hb)⟩
            · have hbv := val_succ_of_ne_zero hb hab
              exact ⟨⟨a.val-1,by omega⟩,(hmem a _).mpr (Or.inr (Or.inl (by simp; omega))),
                (hmem b _).mpr (Or.inr (Or.inr (by simp; omega)))⟩
        intro a b hadj
        rcases (cyc_adj a b).mp hadj with h | h
        · exact key a b h
        · obtain ⟨τ,h1,h2⟩ := key b a h
          exact ⟨τ,h2,h1⟩)
      (by
        intro a τ1 τ2 τ3 h13 h32 h1 h2
        have a1 := (hmem a τ1).mp h1
        have a2 := (hmem a τ2).mp h2
        have b1 : τ1.val ≤ τ3.val := h13
        have b2 : τ3.val ≤ τ2.val := h32
        refine (hmem a τ3).mpr ?_
        by_cases h0 : a = 0
        · exact Or.inl h0
        · right
          have a1' : a.val = τ1.val+1 ∨ a.val = τ1.val+2 := a1.resolve_left h0
          have a2' : a.val = τ2.val+1 ∨ a.val = τ2.val+2 := a2.resolve_left h0
          omega)
  refine ⟨inferInstance,n-3,D,fun τ => ?_⟩
  change (bag τ).card ≤ 3
  have hsub : bag τ ⊆ {0,((τ.val+1 : ℕ) : ZMod n),((τ.val+2 : ℕ) : ZMod n)} := by
    intro a ha
    rcases (hmem a τ).mp ha with h | h | h
    · simp [h]
    · have := ZMod.natCast_zmod_val a
      rw [h] at this
      simp [← this]
    · have := ZMod.natCast_zmod_val a
      rw [h] at this
      simp [← this]
  exact (Finset.card_le_card hsub).trans Finset.card_le_three


end TreewidthHom.OddCycle
