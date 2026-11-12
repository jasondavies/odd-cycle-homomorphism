module

public import TreewidthHom.TreeDecomposition

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- The path between two ordered indices stays in their closed interval. -/
theorem interval_walk {n : ℕ} (a b : Fin n) (hab : a ≤ b) :
    ∃ p : (pathGraph n).Walk a b, ∀ c ∈ p.support, a ≤ c ∧ c ≤ b := by
  let d := b.val-a.val
  let f : pathGraph (d+1) →g pathGraph n :=
    { toFun := fun i => ⟨a.val+i.val,by have := i.isLt; have := b.isLt; change a.val ≤ b.val at hab; dsimp [d] at *; omega⟩
      map_rel' := by
        intro i j h
        apply pathGraph_adj.mpr
        have hh := pathGraph_adj.mp h
        change a.val+i.val+1 = a.val+j.val ∨ a.val+j.val+1 = a.val+i.val
        omega }
  obtain ⟨w⟩ := connected_pathGraph_add_one d 0 (Fin.last d)
  have ha : f 0 = a := by apply Fin.ext; simp [f]
  have hb : f (Fin.last d) = b := by
    apply Fin.ext
    change a.val+d = b.val
    change a.val ≤ b.val at hab
    dsimp [d]
    omega
  refine ⟨(w.map f).copy ha hb,?_⟩
  intro c hc
  have hc' : c ∈ w.support.map f := by simpa only [Walk.support_copy,Walk.support_map] using hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc'
  change a.val ≤ a.val+i.val ∧ a.val+i.val ≤ b.val
  have := i.isLt
  change a.val ≤ b.val at hab
  dsimp [d] at *
  omega

/-- Interval occurrence sets give a decomposition over a path of bag indices. -/
noncomputable def intervalDecomposition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (bag : Fin (n+1) → Finset V)
    (cover : ∀ v, ∃ b, v ∈ bag b)
    (edges : ∀ {u v}, G.Adj u v → ∃ b, u ∈ bag b ∧ v ∈ bag b)
    (convex : ∀ v a b c, a ≤ c → c ≤ b → v ∈ bag a → v ∈ bag b → v ∈ bag c) :
    Decomposition G (pathGraph (n+1)) where
  tree := isTree_pathGraph_add_one n
  bag := bag
  vertex_cover := cover
  edge_cover := edges
  running := by
    intro v a b ha hb
    by_cases h : a ≤ b
    · obtain ⟨p,hp⟩ := interval_walk a b h
      exact ⟨p,fun c hc => convex v a b c (hp c hc).1 (hp c hc).2 ha hb⟩
    · obtain ⟨p,hp⟩ := interval_walk b a (le_of_lt (lt_of_not_ge h))
      refine ⟨p.reverse,?_⟩
      intro c hc
      rw [Walk.support_reverse,List.mem_reverse] at hc
      exact convex v b a c (hp c hc).1 (hp c hc).2 hb ha

/-- The path graph has a width-one decomposition. -/
noncomputable def pathDecomposition (n : ℕ) :
    Decomposition (pathGraph (n+1)) (pathGraph (n+1)) := by
  let bag : Fin (n+1) → Finset (Fin (n+1)) := fun b =>
    Finset.univ.filter (fun v => v.val ≤ b.val ∧ b.val ≤ v.val+1)
  apply intervalDecomposition (pathGraph (n+1)) n bag
  · intro v; exact ⟨v,by simp [bag]⟩
  · intro u v h
    rcases pathGraph_adj.mp h with h | h
    · exact ⟨v,by simp [bag]; omega,by simp [bag]⟩
    · exact ⟨u,by simp [bag],by simp [bag]; omega⟩
  · intro v a b c hac hcb ha hb
    simp only [bag,Finset.mem_filter,Finset.mem_univ,true_and] at *
    change a.val ≤ c.val at hac
    change c.val ≤ b.val at hcb
    omega

theorem pathDecomposition_width (n : ℕ) : ∀ b, ((pathDecomposition n).bag b).card ≤ 2 := by
  intro b
  change (Finset.univ.filter (fun v : Fin (n+1) => v.val ≤ b.val ∧ b.val ≤ v.val+1)).card ≤ 2
  let prev : Fin (n+1) := ⟨b.val-1,by have := b.isLt; omega⟩
  apply le_trans (Finset.card_le_card (t := {b,prev}) ?_) Finset.card_le_two
  intro v hv
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
  simp only [Finset.mem_insert,Finset.mem_singleton]
  by_cases h : v.val = b.val
  · exact Or.inl (Fin.ext h)
  · right
    apply Fin.ext
    dsimp [prev]
    omega

end TreewidthHom
