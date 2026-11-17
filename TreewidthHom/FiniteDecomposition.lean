module

public import TreewidthHom.Parameters
public import TreewidthHom.TreeHelly

@[expose] public section

/-!
# Finite tree-decomposition certificates

For a finite graph, arbitrary-index tree decompositions and finite-index tree
decompositions give the same width. Choose finitely many covering bags, connect
them by finitely many walks, and restrict to the resulting finite subtree.
Relabelling its vertices gives a certificate indexed by `Fin N`.
-/

namespace TreewidthHom
open SimpleGraph

/-- Every finite vertex set in a connected graph lies in a finite connected
induced subgraph. The initial set may be empty. -/
theorem finite_connected_superset {B : Type} {T : SimpleGraph B}
    (hT : T.Connected) (s : Finset B) :
    ∃ S : Finset B, s ⊆ S ∧ (T.induce (S : Set B)).Connected := by
  classical
  let r : B := hT.nonempty.some
  let p : ∀ b : B, T.Walk r b := fun b => (hT r b).some
  let S : Finset B := insert r (s.biUnion (fun b => (p b).support.toFinset))
  have hr : r ∈ S := by simp [S]
  have hsub : ∀ b ∈ s, ∀ x ∈ (p b).support, x ∈ S := by
    intro b hb x hx
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb, by simpa using hx⟩)
  have hreach : ∀ x : (S : Set B), (T.induce (S : Set B)).Reachable ⟨r, hr⟩ x := by
    rintro ⟨x, hx⟩
    have hx' : x = r ∨ x ∈ s.biUnion (fun b => (p b).support.toFinset) :=
      Finset.mem_insert.mp hx
    rcases hx' with rfl | hx'
    · exact Reachable.refl _
    · obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx'
      have hxp : x ∈ (p b).support := by simpa using hxb
      let q := (p b).takeUntil x hxp
      have hq : ∀ y ∈ q.support, y ∈ (S : Set B) :=
        fun y hy => hsub b hb y ((p b).support_takeUntil_subset_support hxp hy)
      exact ⟨q.induce (S : Set B) hq⟩
  let : Nonempty (S : Set B) := ⟨⟨r, hr⟩⟩
  exact ⟨S, fun b hb => hsub b hb b (p b).end_mem_support,
    ⟨fun x y => (hreach x).symm.trans (hreach y)⟩⟩

namespace Decomposition
variable {V B C : Type} [DecidableEq V] {G : SimpleGraph V}
  {T : SimpleGraph B} (D : Decomposition G T)

/-- Restrict the bag tree to a connected set retaining vertex and edge coverage. -/
noncomputable def restrict (S : Set B) (hconn : (T.induce S).Connected)
    (hvertex : ∀ v, ∃ b ∈ S, v ∈ D.bag b)
    (hedge : ∀ {u v}, G.Adj u v → ∃ b ∈ S, u ∈ D.bag b ∧ v ∈ D.bag b) :
    Decomposition G (T.induce S) where
  tree := ⟨hconn, D.tree.isAcyclic.induce S⟩
  bag b := D.bag b.val
  vertex_cover := by
    intro v
    obtain ⟨b, hb, hv⟩ := hvertex v
    exact ⟨⟨b, hb⟩, hv⟩
  edge_cover := by
    intro u v huv
    obtain ⟨b, hb, hu, hv⟩ := hedge huv
    exact ⟨⟨b, hb⟩, hu, hv⟩
  running := by
    classical
    intro v a b ha hb
    obtain ⟨p, hp⟩ := D.running v a.val b.val ha hb
    obtain ⟨q⟩ := hconn a b
    let f := (Embedding.induce (G := T) S).toHom
    have hpath : (q.toPath.val.map f).IsPath := q.toPath.property.map Subtype.val_injective
    refine ⟨q.toPath.val, ?_⟩
    intro c hc
    have hc' : c.val ∈ (q.toPath.val.map f).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact hp c.val (path_support_subset D.tree.isAcyclic _ hpath p hc')

/-- Change only the labels of the decomposition's index tree. -/
noncomputable def reindex (e : C ≃ B) : Decomposition G (T.comap e) where
  tree := (Iso.comap e T).isTree_iff.mpr D.tree
  bag c := D.bag (e c)
  vertex_cover := by
    intro v
    obtain ⟨b, hb⟩ := D.vertex_cover v
    exact ⟨e.symm b, by simpa using hb⟩
  edge_cover := by
    intro u v huv
    obtain ⟨b, hu, hv⟩ := D.edge_cover huv
    exact ⟨e.symm b, by simpa using hu, by simpa using hv⟩
  running := by
    intro v a b ha hb
    obtain ⟨p, hp⟩ := D.running v (e a) (e b) ha hb
    let f := (Iso.comap e T).symm.toHom
    let q := p.map f
    refine ⟨q.copy (by simp [f]) (by simp [f]), ?_⟩
    intro c hc
    simp only [Walk.support_copy, q, Walk.support_map, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    simpa [f] using hp d hd

/-- A finite subtree suffices to witness every coverage obligation. -/
theorem finite_restriction [Fintype V] :
    ∃ S : Finset B, ∃ D' : Decomposition G (T.induce (S : Set B)),
      ∀ b, D'.bag b = D.bag b.val := by
  classical
  let E := {e : V × V // G.Adj e.1 e.2}
  let : Fintype E := Subtype.fintype _
  choose vertex hvertex using D.vertex_cover
  choose edge hedge using fun e : E => D.edge_cover e.property
  let seeds : Finset B := Finset.univ.image vertex ∪ Finset.univ.image edge
  obtain ⟨S, hS, hconn⟩ := finite_connected_superset D.tree.connected seeds
  have hv : ∀ v, ∃ b ∈ (S : Set B), v ∈ D.bag b := by
    intro v
    exact ⟨vertex v, hS (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨v, Finset.mem_univ _, rfl⟩)), hvertex v⟩
  have he : ∀ {u v}, G.Adj u v → ∃ b ∈ (S : Set B), u ∈ D.bag b ∧ v ∈ D.bag b := by
    intro u v huv
    let e : E := ⟨(u, v), huv⟩
    exact ⟨edge e, hS (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨e, Finset.mem_univ _, rfl⟩)), hedge e⟩
  exact ⟨S, D.restrict (S : Set B) hconn hv he, fun _ => rfl⟩

end Decomposition

/-- Width witnessed by a tree decomposition with finitely labelled bags. -/
def HasFiniteWidth {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ d : DecidableEq V, ∃ N : ℕ, ∃ T : SimpleGraph (Fin N),
    ∃ D : @Decomposition V (Fin N) d G T, ∀ b, (D.bag b).card ≤ w + 1

/-- A finite tree certificate with an explicit upper bound on its bag count. -/
def HasWidthWithBags {V : Type} (G : SimpleGraph V) (w N : ℕ) : Prop :=
  ∃ d : DecidableEq V, ∃ K : ℕ, ∃ T : SimpleGraph (Fin K),
    ∃ D : @Decomposition V (Fin K) d G T,
      (∀ b, (D.bag b).card ≤ w+1) ∧ K ≤ N

theorem HasWidthWithBags.hasFiniteWidth {V : Type} {G : SimpleGraph V} {w N : ℕ}
    (h : HasWidthWithBags G w N) : HasFiniteWidth G w := by
  obtain ⟨d, K, T, D, hD, _⟩ := h
  exact ⟨d, K, T, D, hD⟩

theorem HasFiniteWidth.hasWidth {V : Type} {G : SimpleGraph V} {w : ℕ}
    (h : HasFiniteWidth G w) : HasWidth G w := by
  obtain ⟨d, N, T, D, hD⟩ := h
  exact ⟨d, Fin N, T, D, hD⟩

/-- Finite graphs lose no width when the bag-index tree is required to be finite. -/
theorem hasFiniteWidth_iff_hasWidth {V : Type} [Fintype V] {G : SimpleGraph V} {w : ℕ} :
    HasFiniteWidth G w ↔ HasWidth G w := by
  classical
  refine ⟨HasFiniteWidth.hasWidth, ?_⟩
  rintro ⟨d, B, T, D, hD⟩
  let := d
  obtain ⟨S, D', hbag⟩ := D.finite_restriction
  let e := (Fintype.equivFin (S : Set B)).symm
  refine ⟨d, Fintype.card (S : Set B), _, D'.reindex e, ?_⟩
  intro b
  change (D'.bag (e b)).card ≤ _
  rw [hbag]
  exact hD _

theorem finite_decomposition_at_treewidth {V : Type} [Fintype V] (G : SimpleGraph V) :
    HasFiniteWidth G (treewidth G) :=
  hasFiniteWidth_iff_hasWidth.mpr (hasWidth_treewidth G)

end TreewidthHom
