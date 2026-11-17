module

public import TreewidthHom.Parameters

@[expose] public section

/-!
# Graph minors and decomposition transfer

A minor model assigns a nonempty connected branch set to each minor vertex.
Distinct branch sets are disjoint, and each minor edge has an edge between
its branch sets. Connectivity is written using walks in the ambient graph.
-/

namespace TreewidthHom
open SimpleGraph

structure MinorModel {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  nonempty : ∀ w, (branch w).Nonempty
  disjoint : ∀ {u v x}, x ∈ branch u → x ∈ branch v → u = v
  connected : ∀ w x, x ∈ branch w → ∀ y, y ∈ branch w →
    ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ branch w
  edge : ∀ {u v}, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

namespace Decomposition
variable {V B : Type*} [DecidableEq V] {G : SimpleGraph V} {T : SimpleGraph B}

/-- Bags meeting a connected vertex set form a connected subtree. -/
theorem running_set (D : Decomposition G T) (S : Set V) {x y : V}
    (p : G.Walk x y) (hp : ∀ z ∈ p.support, z ∈ S)
    (a b : B) (ha : x ∈ D.bag a) (hb : y ∈ D.bag b) :
    ∃ q : T.Walk a b, ∀ c ∈ q.support, ∃ z ∈ D.bag c, z ∈ S := by
  induction p generalizing a with
  | @nil x =>
    obtain ⟨q, hq⟩ := D.running x a b ha hb
    exact ⟨q, fun c hc => ⟨x, hq c hc, hp x (by simp)⟩⟩
  | @cons x z y hxz p ih =>
    obtain ⟨c, hxc, hzc⟩ := D.edge_cover hxz
    obtain ⟨q, hq⟩ := D.running x a c ha hxc
    obtain ⟨r, hr⟩ := ih (fun t ht => hp t (by simp [ht])) c hzc hb
    refine ⟨q.append r, ?_⟩
    intro d hd
    rcases (Walk.mem_support_append_iff q r).mp hd with hd | hd
    · exact ⟨x, hq d hd, hp x (by simp)⟩
    · exact hr d hd

end Decomposition

namespace MinorModel
variable {V W B : Type} {G : SimpleGraph V} {H : SimpleGraph W}
  {T : SimpleGraph B} (M : MinorModel H G)

/-- A convenient presentation of branch sets as fibres of a partial labelling. -/
noncomputable def ofFibres (label : V → Option W) (root : W → V)
    (hroot : ∀ w, label (root w) = some w)
    (hreach : ∀ w v (hv : label v = some w),
      (G.induce {x | label x = some w}).Reachable ⟨v, hv⟩ ⟨root w, hroot w⟩)
    (hedge : ∀ {u v}, H.Adj u v →
      ∃ x y, label x = some u ∧ label y = some v ∧ G.Adj x y) : MinorModel H G where
  branch w := {v | label v = some w}
  nonempty w := ⟨root w, hroot w⟩
  disjoint := by intro u v x hu hv; exact Option.some.inj (hu.symm.trans hv)
  connected := by
    intro w x hx y hy
    obtain ⟨p⟩ := (hreach w x hx).trans (hreach w y hy).symm
    refine ⟨p.map (Embedding.induce _).toHom, ?_⟩
    intro z hz
    change z ∈ (p.map (Embedding.induce _).toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact z'.property
  edge := by
    intro u v huv
    obtain ⟨x, y, hx, hy, hxy⟩ := hedge huv
    exact ⟨x, hx, y, hy, hxy⟩

noncomputable def bag [Fintype W] (s : Finset V) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => ∃ v ∈ s, v ∈ M.branch w)

@[simp] theorem mem_bag [Fintype W] {s : Finset V} {w : W} :
    w ∈ M.bag s ↔ ∃ v ∈ s, v ∈ M.branch w := by
  classical
  simp [bag]

theorem bag_card_le [Fintype W] (s : Finset V) : (M.bag s).card ≤ s.card := by
  classical
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    let pick : W → V := fun w =>
      if h : ∃ v ∈ s, v ∈ M.branch w then h.choose else Classical.arbitrary V
    have hs : ∀ w ∈ M.bag s, pick w ∈ s ∧ pick w ∈ M.branch w := by
      intro w hw
      have h := M.mem_bag.mp hw
      simp only [pick, dite_eq_left h]
      exact h.choose_spec
    exact Finset.card_le_card_of_injOn pick (fun w hw => (hs w hw).1)
      (fun u hu v hv he => M.disjoint (hs u hu).2 (he ▸ (hs v hv).2))
  · have hempty : M.bag s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      obtain ⟨v, _, _⟩ := M.mem_bag.mp hw
      exact hV ⟨v⟩
    simp [hempty]

/-- Contract each branch set in every bag; the index tree is unchanged. -/
noncomputable def decomposition [DecidableEq V] [DecidableEq W] [Fintype W]
    (D : Decomposition G T) : Decomposition H T where
  tree := D.tree
  bag b := M.bag (D.bag b)
  vertex_cover := by
    intro w
    obtain ⟨v, hv⟩ := M.nonempty w
    obtain ⟨b, hb⟩ := D.vertex_cover v
    exact ⟨b, M.mem_bag.mpr ⟨v, hb, hv⟩⟩
  edge_cover := by
    intro u v huv
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge huv
    obtain ⟨b, hb, hb'⟩ := D.edge_cover hxy
    exact ⟨b, M.mem_bag.mpr ⟨x, hb, hx⟩, M.mem_bag.mpr ⟨y, hb', hy⟩⟩
  running := by
    intro w a b ha hb
    obtain ⟨x, hxa, hx⟩ := M.mem_bag.mp ha
    obtain ⟨y, hyb, hy⟩ := M.mem_bag.mp hb
    obtain ⟨p, hp⟩ := M.connected w x hx y hy
    obtain ⟨q, hq⟩ := D.running_set (M.branch w) p hp a b hxa hyb
    exact ⟨q, fun c hc => M.mem_bag.mpr (hq c hc)⟩

include M

theorem hasWidth [Fintype W] {w : ℕ} (h : HasWidth G w) : HasWidth H w := by
  classical
  obtain ⟨d, B, T, D, hD⟩ := h
  let := d
  exact ⟨inferInstance, B, T, M.decomposition D, fun b => (M.bag_card_le _).trans (hD b)⟩

theorem hasPathWidth [Fintype W] {w : ℕ} (h : HasPathWidth G w) : HasPathWidth H w := by
  classical
  obtain ⟨d, r, D, hD⟩ := h
  let := d
  exact ⟨inferInstance, r, M.decomposition D, fun b => (M.bag_card_le _).trans (hD b)⟩

theorem treewidth_le [Fintype V] [Fintype W] : treewidth H ≤ treewidth G :=
  TreewidthHom.treewidth_le (M.hasWidth (hasWidth_treewidth G))

theorem pathwidth_le [Fintype V] [Fintype W] : pathwidth H ≤ pathwidth G :=
  TreewidthHom.pathwidth_le (M.hasPathWidth (hasPathWidth_pathwidth G))

/-- Reachability lifts through connected branch sets. -/
theorem reachable {u v : W} (h : H.Reachable u v)
    {x y : V} (hx : x ∈ M.branch u) (hy : y ∈ M.branch v) : G.Reachable x y := by
  obtain ⟨p⟩ := h
  induction p generalizing x with
  | nil => obtain ⟨q, _⟩ := M.connected _ x hx y hy; exact ⟨q⟩
  | @cons u v w huv p ih =>
    obtain ⟨a, ha, b, hb, hab⟩ := M.edge huv
    obtain ⟨q, _⟩ := M.connected u x hx a ha
    exact (show G.Reachable x a from ⟨q⟩).trans (hab.reachable.trans (ih hb hy))

private theorem within_branch_delete {u v : W} (huv : u ≠ v)
    {x y : V} (hx : x ∈ M.branch u) (hy : y ∈ M.branch v)
    (w : W) {a b : V} (ha : a ∈ M.branch w) (hb : b ∈ M.branch w) :
    (G.deleteEdges {s(x, y)}).Reachable a b := by
  obtain ⟨p, hp⟩ := M.connected w a ha b hb
  refine reachable_deleteEdges_iff_exists_walk.mpr ⟨p, ?_⟩
  intro he
  have hwu := M.disjoint (hp x (p.fst_mem_support_of_mem_edges he)) hx
  have hwv := M.disjoint (hp y (p.snd_mem_support_of_mem_edges he)) hy
  exact huv (hwu.symm.trans hwv)

/-- A forest remains a forest after taking a minor. -/
theorem isAcyclic (hG : G.IsAcyclic) : H.IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  obtain ⟨x, hx, y, hy, hxy⟩ := M.edge huv
  have bridge := isAcyclic_iff_forall_adj_isBridge.mp hG hxy
  intro hreach
  obtain ⟨p⟩ := hreach
  have lift : ∀ {a b : W} (q : (H.deleteEdges {s(u, v)}).Walk a b)
      {z t : V}, z ∈ M.branch a → t ∈ M.branch b →
      (G.deleteEdges {s(x, y)}).Reachable z t := by
    intro a b q
    induction q with
    | nil =>
      intro z t hz ht
      exact M.within_branch_delete huv.ne hx hy _ hz ht
    | @cons a b c hab q ih =>
      intro z t hz ht
      have hab' := deleteEdges_adj.mp hab
      obtain ⟨r, hr, s, hs, hrs⟩ := M.edge hab'.1
      have hcross : (G.deleteEdges {s(x, y)}).Adj r s := by
        apply deleteEdges_adj.mpr
        refine ⟨hrs, ?_⟩
        intro he
        have he' : s(r, s) = s(x, y) := Set.mem_singleton_iff.mp he
        have he'' : s(a, b) = s(u, v) := by
          rcases Sym2.eq_iff.mp he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [M.disjoint hr hx, M.disjoint hs hy]
          · rw [M.disjoint hr hy, M.disjoint hs hx, Sym2.eq_swap]
        exact hab'.2 (Set.mem_singleton_iff.mpr he'')
      exact (M.within_branch_delete huv.ne hx hy a hz hr).trans
        (hcross.reachable.trans (ih hs ht))
  exact bridge (lift p hx hy)

private theorem avoids [Fintype W] (S : Finset V) {w : W}
    (hw : w ∉ M.bag S) {v : V} (hv : v ∈ M.branch w) : v ∉ S :=
  fun h => hw (M.mem_bag.mpr ⟨v, h, hv⟩)

/-- Delete every minor vertex whose branch meets the deleted ambient vertices. -/
noncomputable def deleteVertices [Fintype W] (S : Finset V) :
    MinorModel (H.induce {w | w ∉ M.bag S}) (G.induce {v | v ∉ S}) where
  branch w := {v | v.val ∈ M.branch w.val}
  nonempty := by
    intro w
    obtain ⟨v, hv⟩ := M.nonempty w.val
    exact ⟨⟨v, M.avoids S w.property hv⟩, hv⟩
  disjoint := by
    intro u v x hu hv
    exact Subtype.ext (M.disjoint hu hv)
  connected := by
    intro w x hx y hy
    obtain ⟨p, hp⟩ := M.connected w.val x.val hx y.val hy
    have havoid : ∀ z ∈ p.support, z ∈ {v | v ∉ S} :=
      fun z hz => M.avoids S w.property (hp z hz)
    refine ⟨p.induce _ havoid, ?_⟩
    intro z hz
    have hz' : z.val ∈ p.support := by simpa only [Walk.support_induce, List.mem_attachWith] using hz
    exact hp z.val hz'
  edge := by
    intro u v huv
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge huv
    exact ⟨⟨x, M.avoids S u.property hx⟩, hx,
      ⟨y, M.avoids S v.property hy⟩, hy, hxy⟩

theorem feedback_transfer [Fintype W] (S : Finset V)
    (hS : (G.induce {v | v ∉ S}).IsAcyclic) :
    (H.induce {w | w ∉ M.bag S}).IsAcyclic ∧ (M.bag S).card ≤ S.card :=
  ⟨(M.deleteVertices S).isAcyclic hS, M.bag_card_le S⟩

theorem fvs_le [Fintype V] [Fintype W] : fvs H ≤ fvs G := by
  obtain ⟨S, hcard, hS⟩ := exists_fvs G
  have h := M.feedback_transfer S hS
  exact (TreewidthHom.fvs_le (M.bag S) h.1).trans (h.2.trans_eq hcard)

end MinorModel
end TreewidthHom
