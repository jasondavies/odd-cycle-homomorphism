module

public import Mathlib

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- An orientation of a forest toward one root in each component. -/
structure ForestOrientation {V : Type} (G : SimpleGraph V) where
  rank : V → ℕ
  parent : V → Option V
  parent_spec : ∀ v u, parent v = some u → G.Adj v u ∧ rank v = rank u+1
  edge : ∀ v u, G.Adj v u → parent v = some u ∨ parent u = some v

/-- Every forest admits a rooted orientation. -/
theorem exists_forestOrientation {V : Type} (G : SimpleGraph V) (hG : G.IsAcyclic) :
    Nonempty (ForestOrientation G) := by
  classical
  let root : V → V := fun v => (G.connectedComponentMk v).nonempty_supp.some
  have reach : ∀ v, G.Reachable (root v) v := by
    intro v
    exact ConnectedComponent.exact (G.connectedComponentMk v).nonempty_supp.some_mem
  have same : ∀ u v, G.Adj u v → root u=root v := by
    intro u v h
    dsimp [root]
    rw [ConnectedComponent.sound h.reachable]
  let rank := fun v => G.dist (root v) v
  have step : ∀ u v, G.Adj u v → rank u=rank v+1 ∨ rank v=rank u+1 := by
    intro u v h
    have hh := hG.dist_eq_dist_add_one_of_adj_of_reachable (root u) h (reach u)
    simpa [rank,← same u v h] using hh
  have unique : ∀ v u z, G.Adj v u → G.Adj v z → rank u < rank v → rank z < rank v → u=z := by
    intro v u z hu hz hru hrz
    obtain ⟨p,hp,hplen⟩ := (reach v).exists_path_of_dist
    have pred : ∀ u, G.Adj v u → rank u < rank v → u=p.penultimate := by
      intro u hu hru
      obtain ⟨q,hq,hqlen⟩ := ((reach v).trans hu.reachable).exists_path_of_dist
      have hvnot : v ∉ q.support := by
        intro hv
        have hh := (G.dist_le (q.takeUntil v hv)).trans (q.length_takeUntil_le_length hv)
        rw [hqlen,show root v=root u from same v u hu] at hh
        have he : G.dist (root u) v=rank v := by dsimp [rank]; rw [same v u hu]
        rw [he] at hh
        change rank v ≤ rank u at hh
        omega
      exact hG.eq_penultimate_of_adj_end hp hu
        (hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hu hvnot)
    exact (pred u hu hru).trans (pred z hz hrz).symm
  let parent : V → Option V := fun v =>
    if h : ∃ u, G.Adj v u ∧ rank u < rank v then some h.choose else none
  have pspec : ∀ v u, parent v=some u → G.Adj v u ∧ rank v=rank u+1 := by
    intro v u h
    dsimp [parent] at h
    split_ifs at h with hh
    have he := Option.some.inj h
    have hp := hh.choose_spec
    rw [he] at hp
    have hs := step v u hp.1
    exact ⟨hp.1,by omega⟩
  have chosen : ∀ v u, G.Adj v u → rank u < rank v → parent v=some u := by
    intro v u hu hr
    have hex : ∃ z, G.Adj v z ∧ rank z < rank v := ⟨u,hu,hr⟩
    have he := unique v hex.choose u hex.choose_spec.1 hu hex.choose_spec.2 hr
    simp [parent,hex,he]
  refine ⟨⟨rank,parent,pspec,?_⟩⟩
  intro v u h
  rcases step v u h with hh | hh
  · exact Or.inl (chosen v u h (by omega))
  · exact Or.inr (chosen u v h.symm (by omega))

end TreewidthHom
