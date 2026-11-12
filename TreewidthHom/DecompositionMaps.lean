module

public import TreewidthHom.TreeDecomposition

@[expose] public section

namespace TreewidthHom.Decomposition
open SimpleGraph
variable {V W B : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} {T : SimpleGraph B}

/-- Relabel the vertices of a decomposition through any bijection that reflects edges. -/
def mapEquiv (D : Decomposition G T) (e : V ≃ W)
    (he : ∀ u v, H.Adj (e u) (e v) → G.Adj u v) : Decomposition H T where
  tree := D.tree
  bag b := (D.bag b).map e.toEmbedding
  vertex_cover := by
    intro v
    obtain ⟨b,hb⟩ := D.vertex_cover (e.symm v)
    refine ⟨b,Finset.mem_map.mpr ⟨e.symm v,hb,?_⟩⟩
    exact e.apply_symm_apply v
  edge_cover := by
    intro u v h
    obtain ⟨b,hu,hv⟩ := D.edge_cover (he (e.symm u) (e.symm v) (by simpa using h))
    exact ⟨b,by simpa using hu,by simpa using hv⟩
  running := by
    intro v a b ha hb
    have ha' : e.symm v ∈ D.bag a := by simpa using ha
    have hb' : e.symm v ∈ D.bag b := by simpa using hb
    obtain ⟨p,hp⟩ := D.running (e.symm v) a b ha' hb'
    exact ⟨p,fun c hc => by simpa using hp c hc⟩

theorem mapEquiv_card (D : Decomposition G T) (e : V ≃ W)
    (he : ∀ u v, H.Adj (e u) (e v) → G.Adj u v) (b : B) :
    ((D.mapEquiv e he).bag b).card = (D.bag b).card := by simp [mapEquiv]

/-- Deleting graph edges preserves a supplied decomposition. -/
def mono (D : Decomposition G T) (G' : SimpleGraph V) (h : G' ≤ G) : Decomposition G' T where
  tree := D.tree
  bag := D.bag
  vertex_cover := D.vertex_cover
  edge_cover := fun he => D.edge_cover (h he)
  running := D.running

/-- Every clique of size at most two fits into a bag. -/
theorem small_clique_bag (D : Decomposition G T) (s : Finset V) (hs : s.card ≤ 2)
    (hc : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v) : ∃ b, s ⊆ D.bag b := by
  classical
  interval_cases hcard : s.card
  · have he : s = ∅ := Finset.card_eq_zero.mp hcard
    let := D.tree.connected.nonempty
    exact ⟨Classical.arbitrary B,by simp [he]⟩
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨b,hb⟩ := D.vertex_cover v
    exact ⟨b,by simpa using hb⟩
  · obtain ⟨u,v,hne,rfl⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨b,hu,hv⟩ := D.edge_cover (hc u (by simp) v (by simp) hne)
    refine ⟨b,?_⟩
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv

end TreewidthHom.Decomposition
