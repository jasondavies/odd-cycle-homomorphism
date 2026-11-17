module

public import TreewidthHom.Join

@[expose] public section

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]
variable (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))

/-- The branch label for the join minor. Unselected reference interiors are
discarded; link interiors belong to the hub at the chosen end. -/
def minorLabel : SourceVertex F L → Option (Fin m ⊕ Fin 2)
  | .inl (.inl (.inl a)) => some (.inr a)
  | .inl (.inl (.inr ((v, d), _))) =>
      if d = ((n - 1 : ℕ) : ZMod n) then some (.inl v) else none
  | .inl (.inr v) => some (.inl v)
  | .inr (l, _) => match l.val with
    | .inl (v, _) => some (.inl v)
    | .inr (u, _) => some (.inl u)

def minorRoot : Fin m ⊕ Fin 2 → SourceVertex F L
  | .inl v => .inl (.inr v)
  | .inr a => .inl (.inl (.inl a))

private theorem domain_reaches (hn : 5 ≤ n) (v : Fin m) (d : ZMod n)
    (hd : d ∉ L v) (c : Fin (n - 3)) :
    ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Reachable
      ⟨.inr (⟨.inl (v, d), hd⟩, c), rfl⟩ ⟨minorRoot F L (.inl v), rfl⟩ := by
  let l : Link F L := ⟨.inl (v, d), hd⟩
  have all : ∀ k, ∀ c : Fin (n - 3), n - 3 - c.val = k →
      ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Reachable
        ⟨.inr (l, c), rfl⟩ ⟨minorRoot F L (.inl v), rfl⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hc
      by_cases hlast : c.val + 1 = n - 3
      · exact Adj.reachable (show (source F L).Adj (.inr (l, c))
          (minorRoot F L (.inl v)) from Or.inr ⟨hlast, rfl⟩)
      · let c' : Fin (n - 3) := ⟨c.val + 1, by have := c.isLt; omega⟩
        have hedge : ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Adj
            ⟨.inr (l, c), rfl⟩ ⟨.inr (l, c'), rfl⟩ := ⟨rfl, Or.inl rfl⟩
        exact hedge.reachable.trans (ih _ (by dsimp [c']; omega) c' rfl)
  exact all _ c rfl

private theorem edge_reaches (u v : Fin m) (huv : u < v ∧ F.Adj u v)
    (c : Fin (n - 3)) :
    ((source F L).induce {x | minorLabel F L x = some (.inl u)}).Reachable
      ⟨.inr (⟨.inr (u, v), huv⟩, c), rfl⟩ ⟨minorRoot F L (.inl u), rfl⟩ := by
  let l : Link F L := ⟨.inr (u, v), huv⟩
  have all : ∀ k, ∀ c : Fin (n - 3), c.val = k →
      ((source F L).induce {x | minorLabel F L x = some (.inl u)}).Reachable
        ⟨.inr (l, c), rfl⟩ ⟨minorRoot F L (.inl u), rfl⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hc
      by_cases hz : c.val = 0
      · exact Adj.reachable (show (source F L).Adj (.inr (l, c))
          (minorRoot F L (.inl u)) from Or.inl ⟨hz, rfl⟩)
      · let c' : Fin (n - 3) := ⟨c.val - 1, by have := c.isLt; omega⟩
        have hedge : ((source F L).induce {x | minorLabel F L x = some (.inl u)}).Adj
            ⟨.inr (l, c), rfl⟩ ⟨.inr (l, c'), rfl⟩ := ⟨rfl, Or.inr (by dsimp [c']; omega)⟩
        exact hedge.reachable.trans (ih _ (by dsimp [c']; omega) c' rfl)
  exact all _ c rfl

private theorem private_step_adj (i : Copies m n) (c c' : Fin (n - 2))
    (hc : c'.val = c.val + 1) :
    (source F L).Adj (.inl (.inl (.inr (i, c)))) (.inl (.inl (.inr (i, c')))) := by
  have he : ((c'.val + 2 : ℕ) : ZMod n) = ((c.val + 2 : ℕ) : ZMod n) + 1 := by
    rw [hc]; push_cast; ring
  rw [← ref_natCast i c, ← ref_natCast i c', he]
  exact base_ref_adj i _

private theorem private_reaches (hn : 5 ≤ n) (v : Fin m)
    (hv : ((n - 1 : ℕ) : ZMod n) ∉ L v) (c : Fin (n - 2)) :
    ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Reachable
      ⟨.inl (.inl (.inr ((v, ((n - 1 : ℕ) : ZMod n)), c))), by simp [minorLabel]⟩
      ⟨minorRoot F L (.inl v), rfl⟩ := by
  let d : ZMod n := ((n - 1 : ℕ) : ZMod n)
  let l : Link F L := ⟨.inl (v, d), hv⟩
  have all : ∀ k, ∀ c : Fin (n - 2), n - 2 - c.val = k →
      ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Reachable
        ⟨.inl (.inl (.inr ((v, d), c))), by simp [minorLabel, d]⟩
        ⟨minorRoot F L (.inl v), rfl⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hc
      by_cases hlast : c.val + 1 = n - 2
      · have href : ref (v, d) d = .inr ((v, d), c) := by
          have he : c.val + 2 = n - 1 := by omega
          simpa only [he, d] using ref_natCast (v, d) c
        let c0 : Fin (n - 3) := ⟨0, by omega⟩
        have hedge : ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Adj
            ⟨.inl (.inl (.inr ((v, d), c))), by simp [minorLabel, d]⟩
            ⟨.inr (l, c0), rfl⟩ := Or.inl ⟨rfl, by simp only [l, src, href]⟩
        exact hedge.reachable.trans (domain_reaches F L hn v d hv c0)
      · let c' : Fin (n - 2) := ⟨c.val + 1, by have := c.isLt; omega⟩
        have hedge : ((source F L).induce {x | minorLabel F L x = some (.inl v)}).Adj
            ⟨.inl (.inl (.inr ((v, d), c))), by simp [minorLabel, d]⟩
            ⟨.inl (.inl (.inr ((v, d), c'))), by simp [minorLabel, d]⟩ :=
          private_step_adj F L (v, d) c c' rfl
        exact hedge.reachable.trans (ih _ (by dsimp [c']; omega) c' rfl)
  exact all _ c rfl

private theorem minor_reaches (hn : 5 ≤ n)
    (hL : ∀ v, ((n - 1 : ℕ) : ZMod n) ∉ L v)
    (w : Fin m ⊕ Fin 2) (x : SourceVertex F L) (hx : minorLabel F L x = some w) :
    ((source F L).induce {x | minorLabel F L x = some w}).Reachable
      ⟨x, hx⟩ ⟨minorRoot F L w, by cases w <;> rfl⟩ := by
  rcases x with ((a | ⟨⟨v, d⟩, c⟩) | v) | ⟨⟨(⟨v, d⟩ | ⟨u, v⟩), hl⟩, c⟩
  · have he : .inr a = w := Option.some.inj hx
    subst w
    exact Reachable.refl _
  · dsimp [minorLabel] at hx
    split_ifs at hx with hd
    have he : .inl v = w := Option.some.inj hx
    subst w
    subst d
    exact private_reaches F L hn v (hL v) c
  · have he : .inl v = w := Option.some.inj hx
    subst w
    exact Reachable.refl _
  · have he : .inl v = w := Option.some.inj hx
    subst w
    exact domain_reaches F L hn v d hl c
  · have he : .inl u = w := Option.some.inj hx
    subst w
    exact edge_reaches F L u v hl c

private theorem hub_anchor_edge (hn : 5 ≤ n) (v : Fin m) (a : Fin 2) :
    ∃ x, minorLabel F L x = some (.inl v) ∧
      (source F L).Adj x (minorRoot F L (.inr a)) := by
  let d : ZMod n := ((n - 1 : ℕ) : ZMod n)
  have hd1 : d + 1 = 0 := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · let c : Fin (n - 2) := ⟨n - 3, by omega⟩
    have href : ref (v, d) d = .inr ((v, d), c) := by
      have he : c.val + 2 = n - 1 := by dsimp [c]; omega
      simpa only [he, d] using ref_natCast (v, d) c
    refine ⟨.inl (.inl (.inr ((v, d), c))), by simp [minorLabel, d], ?_⟩
    have h := base_ref_adj (m := m) (v, d) d
    change (base m n).Adj _ _
    simpa only [href, hd1, ref_zero] using h
  · let c : Fin (n - 2) := ⟨0, by omega⟩
    have href : ref (v, d) (1 + 1) = .inr ((v, d), c) := by
      simpa only [c, Nat.cast_add, Nat.cast_ofNat, zero_add, one_add_one_eq_two] using ref_natCast (v, d) c
    refine ⟨.inl (.inl (.inr ((v, d), c))), by simp [minorLabel, d], ?_⟩
    have h := (base_ref_adj (m := m) (v, d) 1).symm
    change (base m n).Adj _ _
    simpa only [href, ref_one] using h

private theorem minor_edge (hn : 5 ≤ n) {u v : Fin m ⊕ Fin 2}
    (huv : (twoApex F).Adj u v) :
    ∃ x y, minorLabel F L x = some u ∧ minorLabel F L y = some v ∧
      (source F L).Adj x y := by
  have edge_case : ∀ u v : Fin m, u < v → F.Adj u v →
      ∃ x y, minorLabel F L x = some (.inl u) ∧ minorLabel F L y = some (.inl v) ∧
        (source F L).Adj x y := by
    intro u v hlt hadj
    let l : Link F L := ⟨.inr (u, v), hlt, hadj⟩
    let c : Fin (n - 3) := ⟨n - 4, by omega⟩
    exact ⟨.inr (l, c), minorRoot F L (.inl v), rfl, rfl,
      Or.inr ⟨by dsimp [c]; omega, rfl⟩⟩
  rcases u with u | a <;> rcases v with v | b
  · have hadj : F.Adj u v := huv
    rcases lt_or_gt_of_ne hadj.ne with hlt | hlt
    · exact edge_case u v hlt hadj
    · obtain ⟨x, y, hx, hy, hxy⟩ := edge_case v u hlt hadj.symm
      exact ⟨y, x, hy, hx, hxy.symm⟩
  · obtain ⟨x, hx, hxa⟩ := hub_anchor_edge F L hn u b
    exact ⟨x, minorRoot F L (.inr b), hx, rfl, hxa⟩
  · obtain ⟨y, hy, hya⟩ := hub_anchor_edge F L hn v a
    exact ⟨minorRoot F L (.inr a), y, rfl, hy, hya.symm⟩
  · refine ⟨minorRoot F L (.inr a), minorRoot F L (.inr b), rfl, rfl, ?_⟩
    have hab : a ≠ b := huv
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact base_anchor_adj
    · exact base_anchor_adj.symm
    · exact (hab rfl).elim

/-- Palette padding supplies a model of the input joined to two adjacent apices.
The hypothesis is explicit: the generic constructor also permits full lists. -/
theorem join_minor (hn : 5 ≤ n)
    (hL : ∀ v, ((n - 1 : ℕ) : ZMod n) ∉ L v) : Nonempty (MinorModel (twoApex F) (source F L)) := by
  exact ⟨MinorModel.ofFibres (minorLabel F L) (minorRoot F L) (fun w => by cases w <;> rfl)
    (minor_reaches F L hn hL) (minor_edge F L hn)⟩

end TreewidthHom.OddCycle.ListReduction
