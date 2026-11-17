module

public import TreewidthHom.BinaryTarget

@[expose] public section

namespace TreewidthHom.OddCycle
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- An odd closed walk contains an odd cycle of no greater length. -/
theorem odd_cycle_of_odd_closed_walk {a : V} (w : G.Walk a a) (hodd : Odd w.length) :
    ∃ (b : V) (c : G.Walk b b), c.IsCycle ∧ Odd c.length ∧ c.length ≤ w.length := by
  have main : ∀ k, ∀ (a : V) (w : G.Walk a a), w.length = k → Odd k →
      ∃ (b : V) (c : G.Walk b b), c.IsCycle ∧ Odd c.length ∧ c.length ≤ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a w hlen hodd
      cases w with
      | nil => norm_num [← hlen] at hodd
      | @cons _ b _ hab p =>
        have hlen' : p.length + 1 = k := hlen
        by_cases hp : p.IsPath
        · have hpos : 0 < p.length := by
            by_contra h
            have hnil : p.Nil := Walk.length_eq_zero_iff.mp (by omega)
            exact hab.ne hnil.eq.symm
          have hk : 3 ≤ k := by obtain ⟨r, hr⟩ := hodd; omega
          refine ⟨a, .cons hab p, ?_, by simpa only [hlen] using hodd, hlen.le⟩
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          exact ⟨by simpa using hp, by simpa only [hlen] using hk⟩
        · have hex : ∃ (v : V) (q : G.Walk v v), q.IsSubwalk p ∧ ¬q.Nil := by
            simpa only [Walk.isPath_iff_isSubwalk_imp_nil, not_forall, not_imp, exists_prop] using hp
          obtain ⟨v, q, ⟨r, s, he⟩, hq⟩ := hex
          have hqpos : 0 < q.length := by
            by_contra h
            exact hq (Walk.length_eq_zero_iff.mp (by omega))
          have he_len : p.length = r.length + q.length + s.length := by
            rw [he, Walk.length_append, Walk.length_append]
          by_cases hqodd : Odd q.length
          · obtain ⟨z, c, hc, hcodd, hclen⟩ := ih q.length (by omega) v q rfl hqodd
            exact ⟨z, c, hc, hcodd, by omega⟩
          · let short : G.Walk a a := .cons hab (r.append s)
            have hshort : short.length = r.length + s.length + 1 := by simp [short, Walk.length_append]
            have hshortodd : Odd short.length := by
              rw [Nat.odd_iff] at hodd hqodd ⊢
              omega
            obtain ⟨z, c, hc, hcodd, hclen⟩ :=
              ih short.length (by omega) a short rfl hshortodd
            exact ⟨z, c, hc, hcodd, by omega⟩
  exact main w.length a w rfl hodd

/-- Odd girth, with value infinity when there is no odd cycle. -/
noncomputable def oddGirth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ (_ : w.IsCycle), ⨅ (_ : Odd w.length), (w.length : ℕ∞)

theorem le_oddGirth {n : ℕ∞} : n ≤ oddGirth G ↔
    ∀ (a : V) (w : G.Walk a a), w.IsCycle → Odd w.length → n ≤ (w.length : ℕ∞) := by
  simp [oddGirth]

theorem oddGirth_le_of_odd_closed_walk {a : V} (w : G.Walk a a) (hodd : Odd w.length) :
    oddGirth G ≤ (w.length : ℕ∞) := by
  obtain ⟨b, c, hc, hcodd, hlen⟩ := odd_cycle_of_odd_closed_walk w hodd
  exact (le_oddGirth.mp le_rfl b c hc hcodd).trans (by exact_mod_cast hlen)

theorem exists_oddGirth_eq_length (h : oddGirth G ≠ ⊤) :
    ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ Odd w.length ∧ oddGirth G = w.length := by
  simp_rw [oddGirth, iInf_subtype', iInf_sigma', ENat.iInf_natCast_ne_top,
    ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
  exact ciInf_mem _

/-- Read a closed walk periodically to obtain a cycle homomorphism. -/
def homOfClosedWalk {n : ℕ} [Fact (1 < n)] {a : V} (w : G.Walk a a)
    (hlen : w.length = n) : cyc n →g G where
  toFun x := w.getVert x.val
  map_rel' := by
    have step : ∀ x y : ZMod n, y = x + 1 → G.Adj (w.getVert x.val) (w.getVert y.val) := by
      intro x y hy
      have hv : y.val = (x.val + 1) % n := by rw [hy, ZMod.val_add, ZMod.val_one]
      have hx := ZMod.val_lt x
      have hadj := w.adj_getVert_succ (by omega : x.val < w.length)
      by_cases hsmall : x.val + 1 < n
      · rw [Nat.mod_eq_of_lt hsmall] at hv
        rwa [hv]
      · have he : x.val + 1 = n := by omega
        have hz : y.val = 0 := by simp [hv, he]
        rw [he.trans hlen.symm, Walk.getVert_length] at hadj
        simpa only [hz, Walk.getVert_zero] using hadj
    intro x y hxy
    rcases (cyc_adj _ _).mp hxy with h | h
    · exact step x y h
    · exact (step y x h).symm

/-- The image of the canonical cycle traversal is a closed walk of the same length. -/
theorem closed_walk_of_cycle_hom {n : ℕ} [Fact (1 < n)] (hn : 3 ≤ n)
    (f : cyc n →g G) : ∃ (a : V) (w : G.Walk a a), w.length = n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hg : cyc (k + 3) = cycleGraph (k + 3) := cyc_eq_cycleGraph (k + 2)
  let f' : cycleGraph (k + 3) →g G := hg ▸ f
  exact ⟨f' 0, (cycleGraph.cycle k).map f', by rw [Walk.length_map, cycleGraph.length_cycle]⟩

theorem oddGirth_le_of_cycle_hom {n : ℕ} [Fact (1 < n)] (hodd : Odd n)
    (f : cyc n →g G) : oddGirth G ≤ (n : ℕ∞) := by
  have hn : 3 ≤ n := by have := Fact.out (p := 1 < n); obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨a, w, hw⟩ := closed_walk_of_cycle_hom hn f
  have h := oddGirth_le_of_odd_closed_walk w (hw ▸ hodd)
  simpa only [hw] using h

end TreewidthHom.OddCycle
