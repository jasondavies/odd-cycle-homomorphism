module

public import TreewidthHom.PathWidth

@[expose] public section

namespace TreewidthHom
open SimpleGraph

theorem path_mem_between {N : ℕ} {a b c : Fin N} (p : (pathGraph N).Walk a b)
    (ha : a ≤ c) (hb : c ≤ b) : c ∈ p.support := by
  induction p with
  | @nil u => have : c=u := le_antisymm hb ha; simp [this]
  | @cons a a' b h p ih =>
    by_cases he : c=a
    · simp [he]
    · apply List.mem_cons_of_mem
      apply ih ?_ hb
      have hh := pathGraph_adj.mp h
      have ha' : a.val ≤ c.val := ha
      have he' : c.val ≠ a.val := fun hh => he (Fin.ext hh)
      change a'.val ≤ c.val
      omega

theorem Decomposition.path_convex {V : Type} [DecidableEq V] {G : SimpleGraph V} {R : ℕ}
    (D : Decomposition G (pathGraph (R+1))) (v : V) (a b c : Fin (R+1))
    (ha : a ≤ c) (hb : c ≤ b) (hva : v ∈ D.bag a) (hvb : v ∈ D.bag b) : v ∈ D.bag c := by
  obtain ⟨p,hp⟩ := D.running v a b hva hvb
  exact hp c (path_mem_between p ha hb)

/-- The endpoint representation of any supplied path decomposition. -/
theorem Decomposition.path_intervals {V : Type} [DecidableEq V] {G : SimpleGraph V} {R : ℕ}
    (D : Decomposition G (pathGraph (R+1))) :
    ∃ lo hi : V → ℕ, (∀ v, lo v ≤ hi v) ∧ (∀ v, hi v ≤ R) ∧
      ∀ v (t : Fin (R+1)), v ∈ D.bag t ↔ lo v ≤ t.val ∧ t.val ≤ hi v := by
  classical
  let times : V → Finset (Fin (R+1)) := fun v => Finset.univ.filter (fun t => v ∈ D.bag t)
  have hne : ∀ v, (times v).Nonempty := by
    intro v; obtain ⟨b,hb⟩ := D.vertex_cover v; exact ⟨b,by simp [times,hb]⟩
  let first := fun v => (times v).min' (hne v)
  let last := fun v => (times v).max' (hne v)
  have hf : ∀ v, v ∈ D.bag (first v) := by
    intro v; have := Finset.min'_mem (times v) (hne v); simpa [times] using this
  have hl : ∀ v, v ∈ D.bag (last v) := by
    intro v; have := Finset.max'_mem (times v) (hne v); simpa [times] using this
  refine ⟨fun v => (first v).val,fun v => (last v).val,?_,?_,?_⟩
  · intro v
    exact Finset.min'_le (times v) (last v) (Finset.max'_mem (times v) (hne v))
  · intro v; change (last v).val ≤ R; have := (last v).isLt; omega
  · intro v t
    constructor
    · intro ht
      have hm : t ∈ times v := by simp [times,ht]
      exact ⟨Finset.min'_le _ _ hm,Finset.le_max' _ _ hm⟩
    · rintro ⟨h1,h2⟩
      exact D.path_convex v (first v) (last v) t h1 h2 (hf v) (hl v)

theorem pathWidth_of_intervals_bag_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    (P w : ℕ) (lo hi : V → ℕ) (hlohi : ∀ v, lo v ≤ hi v) (hhi : ∀ v, hi v ≤ P)
    (hedge : ∀ u v, G.Adj u v → lo u ≤ hi v ∧ lo v ≤ hi u)
    (hcard : ∀ p, (Finset.univ.filter (fun v => lo v ≤ p ∧ p ≤ hi v)).card ≤ w+1) :
    HasPathWidthWithBags G w (P+1) := by
  classical
  let bag := fun p : Fin (P+1) => Finset.univ.filter (fun v => lo v ≤ p.val ∧ p.val ≤ hi v)
  let D := intervalDecomposition G P bag
    (fun v => ⟨⟨lo v,by have := hlohi v; have := hhi v; omega⟩,by simp [bag,hlohi v]⟩)
    (by
      intro u v h
      have hh := hedge u v h
      let p := max (lo u) (lo v)
      have hu : p ≤ hi u := max_le (hlohi u) hh.2
      have hv : p ≤ hi v := max_le hh.1 (hlohi v)
      refine ⟨⟨p,by have := hhi u; omega⟩,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_max_left _ _,hu⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_max_right _ _,hv⟩)
    (by
      intro v a b c h1 h2 ha hb
      simp only [bag,Finset.mem_filter,Finset.mem_univ,true_and] at *
      have h1' : a.val ≤ c.val := h1
      have h2' : c.val ≤ b.val := h2
      omega)
  exact ⟨inferInstance,P,D,(fun p => hcard p.val),le_rfl⟩

theorem hasPathWidth_of_intervals {V : Type} [Fintype V] (G : SimpleGraph V)
    (P w : ℕ) (lo hi : V → ℕ) (hlohi : ∀ v, lo v ≤ hi v) (hhi : ∀ v, hi v ≤ P)
    (hedge : ∀ u v, G.Adj u v → lo u ≤ hi v ∧ lo v ≤ hi u)
    (hcard : ∀ p, (Finset.univ.filter (fun v => lo v ≤ p ∧ p ≤ hi v)).card ≤ w+1) :
    HasPathWidth G w := by
  exact (pathWidth_of_intervals_bag_bound G P w lo hi hlohi hhi hedge hcard).hasPathWidth

/-- A general path-decomposition transfer for subdivisions. -/
theorem pathWidth_linked_of_bags_bound {V L : Type} [Fintype V] [Fintype L]
    {G : SimpleGraph V} (H : SimpleGraph V) (hH : H ≤ G)
    (s t : L → V) (q : ℕ) (hq : 0 < q) {w N : ℕ} (hw : HasPathWidthWithBags G w N)
    (hedge : ∀ l, G.Adj (s l) (t l)) : HasPathWidthWithBags (linked H s t q) (w+2) (N*((Fintype.card L+1)*(q+1))) := by
  classical
  obtain ⟨d,R,D,hw,hN⟩ := hw
  obtain ⟨lo,hi,hlohi,hhi,hmem⟩ := D.path_intervals
  choose owner hs ht using fun l => D.edge_cover (hedge l)
  have hb : ∀ p, (Finset.univ.filter (fun v => lo v ≤ p ∧ p ≤ hi v)).card ≤ w+1 := by
    intro p
    by_cases hp : p ≤ R
    · have he : Finset.univ.filter (fun v => lo v ≤ p ∧ p ≤ hi v) = D.bag ⟨p,by omega⟩ := by
        ext v; simp [hmem]
      rw [he]; exact hw _
    · have he : Finset.univ.filter (fun v => lo v ≤ p ∧ p ≤ hi v) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        have hh : p ≤ hi v := (Finset.mem_filter.mp hv).2.2
        have := hhi v; omega
      simp [he]
  have h : HasPathWidthWithBags (linked H s t q) (w+2)
      ((R+1)*((Fintype.card L+1)*(q+1))) := by
    apply pathWidth_linked_bag_bound H s t q hq R (Fintype.card L) (w+2) lo hi hlohi hhi
      (fun u v h => ?_) (fun l => (owner l).val) (fun l => (Fintype.equivFin L l).val)
      (fun l => (Fintype.equivFin L l).isLt) (fun l l' _ h => (Fintype.equivFin L).injective (Fin.ext h))
      (fun l => (hmem _ _).mp (hs l)) (fun l => (hmem _ _).mp (ht l))
      (fun p => by have := hb p; omega) (fun l => by have := hb (owner l).val; omega)
    obtain ⟨b,hu,hv⟩ := D.edge_cover (hH h)
    have hu' := (hmem _ _).mp hu
    have hv' := (hmem _ _).mp hv
    omega
  obtain ⟨d', r, D', hD', hr⟩ := h
  exact ⟨d', r, D', hD', hr.trans (Nat.mul_le_mul_right _ hN)⟩

theorem pathWidth_linked_of_bags {V L : Type} [Fintype V] [Fintype L]
    {G : SimpleGraph V} (H : SimpleGraph V) (hH : H ≤ G)
    (s t : L → V) (q : ℕ) (hq : 0 < q) {w : ℕ} (hw : HasPathWidth G w)
    (hedge : ∀ l, G.Adj (s l) (t l)) : HasPathWidth (linked H s t q) (w+2) := by
  classical
  obtain ⟨d, R, D, hD⟩ := hw
  exact (pathWidth_linked_of_bags_bound H hH s t q hq
    ⟨d, R, D, hD, le_rfl⟩ hedge).hasPathWidth

end TreewidthHom
