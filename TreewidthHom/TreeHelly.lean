module

public import TreewidthHom.TreeDecomposition

@[expose] public section

namespace TreewidthHom
open SimpleGraph

variable {B : Type*} {T : SimpleGraph B}

/-- The unique path in a forest is contained in every walk with the same ends. -/
theorem path_support_subset (hT : T.IsAcyclic) {a b : B} (p : T.Walk a b)
    (hp : p.IsPath) (q : T.Walk a b) : p.support ⊆ q.support := by
  classical
  have he := (hT.subsingleton_path a b).elim (⟨p, hp⟩ : T.Path a b) q.toPath
  have he' : p = q.toPath.val := congrArg Subtype.val he
  rw [he']
  exact q.support_toPath_subset_support

/-- Three pairwise connecting paths in a tree share a vertex. -/
theorem tree_path_median (hT : T.IsAcyclic) {a b c : B}
    (p : T.Walk a b) (hp : p.IsPath) (q : T.Walk a c) (hq : q.IsPath)
    (r : T.Walk b c) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support ∧ x ∈ r.support := by
  classical
  induction p generalizing c with
  | @nil a => exact ⟨a, by simp, q.start_mem_support, r.start_mem_support⟩
  | @cons a a' b haa p ih =>
    obtain ⟨hp, hpa⟩ := (Walk.cons_isPath_iff _ _).mp hp
    cases q with
    | nil => exact ⟨a, by simp, by simp, r.end_mem_support⟩
    | @cons _ a'' c hab q =>
      obtain ⟨hq, hqa⟩ := (Walk.cons_isPath_iff _ _).mp hq
      by_cases he : a' = a''
      · subst a''
        obtain ⟨x, hx, hx', hxr⟩ := ih hp q hq r
        exact ⟨x, by simp [hx], by simp [hx'], hxr⟩
      · refine ⟨a, by simp, by simp, ?_⟩
        by_contra har
        let w := p.append (r.append q.reverse)
        have haw : a ∉ w.support := by
          simp only [w, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
          tauto
        let short : T.Walk a' a'' := .cons haa.symm (.cons hab .nil)
        have hshort : short.IsPath := by
          simp [short, Walk.cons_isPath_iff, haa.ne', hab.ne, he]
        have ha : a ∈ short.support := by simp [short]
        exact haw (path_support_subset hT short hshort w ha)

/-- Nonempty connected vertex sets, expressed by internal walks. -/
def TreeSet (T : SimpleGraph B) (S : Set B) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, ∃ p : T.Walk a b, ∀ x ∈ p.support, x ∈ S

theorem treeSet_inter (hT : T.IsAcyclic) {S U : Set B}
    (hS : TreeSet T S) (hU : TreeSet T U) (hne : (S ∩ U).Nonempty) :
    TreeSet T (S ∩ U) := by
  classical
  refine ⟨hne, ?_⟩
  intro a ha b hb
  obtain ⟨p, hp⟩ := hS.2 a ha.1 b hb.1
  obtain ⟨q, hq⟩ := hU.2 a ha.2 b hb.2
  refine ⟨p.toPath.val, fun x hx => ⟨hp x (p.support_toPath_subset_support hx), ?_⟩⟩
  exact hq x (path_support_subset hT p.toPath.val p.toPath.property q hx)

theorem treeSet_helly_three (hT : T.IsAcyclic) {S U W : Set B}
    (hS : TreeSet T S) (hU : TreeSet T U) (hW : TreeSet T W)
    (hSU : (S ∩ U).Nonempty) (hUW : (U ∩ W).Nonempty) (hSW : (S ∩ W).Nonempty) :
    ∃ x, x ∈ S ∧ x ∈ U ∧ x ∈ W := by
  classical
  obtain ⟨a, haS, haU⟩ := hSU
  obtain ⟨b, hbU, hbW⟩ := hUW
  obtain ⟨c, hcS, hcW⟩ := hSW
  obtain ⟨p, hp⟩ := hU.2 a haU b hbU
  obtain ⟨q, hq⟩ := hS.2 a haS c hcS
  obtain ⟨r, hr⟩ := hW.2 b hbW c hcW
  obtain ⟨x, hxp, hxq, hxr⟩ := tree_path_median hT p.toPath.val p.toPath.property
    q.toPath.val q.toPath.property r
  exact ⟨x, hq x (q.support_toPath_subset_support hxq),
    hp x (p.support_toPath_subset_support hxp), hr x hxr⟩

/-- Finite Helly property for subtrees. -/
theorem treeSet_helly (hT : T.IsTree) {I : Type*} (s : Finset I) (S : I → Set B)
    (hS : ∀ i ∈ s, TreeSet T (S i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (S i ∩ S j).Nonempty) :
    ∃ x, ∀ i ∈ s, x ∈ S i := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact ⟨hT.connected.nonempty.some, by simp⟩
  | @insert i s hi ih =>
    let U := fun j => S i ∩ S j
    have hU : ∀ j ∈ s, TreeSet T (U j) := by
      intro j hj
      exact treeSet_inter hT.isAcyclic (hS i (by simp)) (hS j (by simp [hj]))
        (hpair i (by simp) j (by simp [hj]))
    have hUpair : ∀ j ∈ s, ∀ k ∈ s, (U j ∩ U k).Nonempty := by
      intro j hj k hk
      obtain ⟨x, hx, hxj, hxk⟩ := treeSet_helly_three hT.isAcyclic
        (hS i (by simp)) (hS j (by simp [hj])) (hS k (by simp [hk]))
        (hpair i (by simp) j (by simp [hj]))
        (hpair j (by simp [hj]) k (by simp [hk]))
        (hpair i (by simp) k (by simp [hk]))
      exact ⟨x, ⟨hx, hxj⟩, ⟨hx, hxk⟩⟩
    by_cases hs : s.Nonempty
    · obtain ⟨x, hx⟩ := ih U hU hUpair
      obtain ⟨j, hj⟩ := hs
      refine ⟨x, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (hx j hj).1
      · exact (hx k hk).2
    · obtain ⟨x, hx⟩ := (hS i (by simp)).1
      exact ⟨x, by simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using hx⟩

/-- Every finite clique occurs together in a bag. -/
theorem Decomposition.clique_bag {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D : Decomposition G T) (s : Finset V)
    (hs : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v) : ∃ b, s ⊆ D.bag b := by
  have hsets : ∀ v, TreeSet T {b | v ∈ D.bag b} := by
    intro v
    exact ⟨D.vertex_cover v, fun a ha b hb => D.running v a b ha hb⟩
  exact treeSet_helly D.tree s (fun v => {b | v ∈ D.bag b}) (fun v _ => hsets v) (by
    intro u hu v hv
    by_cases he : u = v
    · subst v
      obtain ⟨b, hb⟩ := D.vertex_cover u
      exact ⟨b, hb, hb⟩
    · exact D.edge_cover (hs u hu v hv he))

end TreewidthHom
