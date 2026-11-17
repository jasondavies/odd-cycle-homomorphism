module

public import TreewidthHom.Join
public import TreewidthHom.TreeHelly

@[expose] public section

namespace TreewidthHom
open SimpleGraph

namespace Decomposition
variable {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq (V ⊕ A)] [Fintype A]
  {G : SimpleGraph V} {T : SimpleGraph B} (D : Decomposition (apexJoin (A := A) G) T)

omit [DecidableEq V] [DecidableEq A] in
theorem apex_clique_bag (s : Finset V)
    (hs : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v) :
    ∃ b, (∀ v ∈ s, Sum.inl v ∈ D.bag b) ∧ ∀ a : A, Sum.inr a ∈ D.bag b := by
  obtain ⟨b, hb⟩ := D.clique_bag (s.disjSum Finset.univ) (by
    rintro (u | u) hu (v | v) hv hne
    · exact hs u (by simpa using hu) v (by simpa using hv) (fun he => hne (congrArg Sum.inl he))
    · trivial
    · trivial
    · exact fun he => hne (congrArg Sum.inr he))
  exact ⟨b, fun v hv => hb (by simp [hv]), fun a => hb (by simp)⟩

noncomputable def withoutApicesBag (b : B) : Finset V := by
  classical
  exact if ∀ a : A, Sum.inr a ∈ D.bag b then (D.bag b).toLeft else ∅

omit [DecidableEq V] [DecidableEq A] in
@[simp] theorem mem_withoutApicesBag {b : B} {v : V} :
    v ∈ D.withoutApicesBag b ↔ Sum.inl v ∈ D.bag b ∧ ∀ a : A, Sum.inr a ∈ D.bag b := by
  classical
  by_cases h : ∀ a : A, Sum.inr a ∈ D.bag b <;> simp [withoutApicesBag, h]

/-- Keep only bags containing the apex clique, and remove that clique.
All other bags become empty, so the original index tree (or path) is retained. -/
noncomputable def withoutApices : Decomposition G T where
  tree := D.tree
  bag := D.withoutApicesBag
  vertex_cover := by
    intro v
    obtain ⟨b, hb, ha⟩ := D.apex_clique_bag {v} (by simp)
    exact ⟨b, D.mem_withoutApicesBag.mpr ⟨hb v (by simp), ha⟩⟩
  edge_cover := by
    intro u v huv
    obtain ⟨b, hb, ha⟩ := D.apex_clique_bag {u, v} (by
      intro x hx y hy hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact huv
      · exact huv.symm
      · exact (hne rfl).elim)
    exact ⟨b, D.mem_withoutApicesBag.mpr ⟨hb u (by simp), ha⟩,
      D.mem_withoutApicesBag.mpr ⟨hb v (by simp), ha⟩⟩
  running := by
    classical
    intro v a b ha hb
    obtain ⟨hva, haa⟩ := D.mem_withoutApicesBag.mp ha
    obtain ⟨hvb, hab⟩ := D.mem_withoutApicesBag.mp hb
    obtain ⟨p, hp⟩ := D.running (.inl v) a b hva hvb
    refine ⟨p.toPath.val, ?_⟩
    intro c hc
    apply D.mem_withoutApicesBag.mpr
    refine ⟨hp c (p.support_toPath_subset_support hc), ?_⟩
    intro x
    obtain ⟨q, hq⟩ := D.running (.inr x) a b (haa x) (hab x)
    exact hq c (path_support_subset D.tree.isAcyclic p.toPath.val p.toPath.property q hc)

omit [DecidableEq V] [DecidableEq A] in
theorem apex_card_le_width [Nonempty V] {w : ℕ} (hw : ∀ b, (D.bag b).card ≤ w + 1) :
    Fintype.card A ≤ w := by
  classical
  let v := Classical.arbitrary V
  obtain ⟨b, hb, ha⟩ := D.apex_clique_bag {v} (by simp)
  have hsub : ({v} : Finset V).disjSum (Finset.univ : Finset A) ⊆ D.bag b := by
    rintro (x | a) hx
    · exact hb x (by simpa using hx)
    · exact ha a
  have := (Finset.card_le_card hsub).trans (hw b)
  simp only [Finset.card_disjSum, Finset.card_singleton, Finset.card_univ] at this
  omega

omit [DecidableEq A] in
theorem withoutApices_card {w : ℕ} (hw : ∀ b, (D.bag b).card ≤ w + 1)
    (hAw : Fintype.card A ≤ w) (b : B) :
    ((D.withoutApices).bag b).card ≤ (w - Fintype.card A) + 1 := by
  classical
  change (D.withoutApicesBag b).card ≤ _
  unfold withoutApicesBag
  split_ifs with h
  · have he : (D.bag b).toRight = (Finset.univ : Finset A) := by ext a; simp [h a]
    have hc := (D.bag b).card_toLeft_add_card_toRight
    rw [he, Finset.card_univ] at hc
    have := hw b
    omega
  · simp

end Decomposition

section
variable {V A : Type} [Fintype V] [Nonempty V] [Fintype A] (G : SimpleGraph V)

theorem treewidth_apexJoin : treewidth (apexJoin (A := A) G) = treewidth G + Fintype.card A := by
  classical
  apply le_antisymm
  · obtain ⟨d, B, T, D, hD⟩ := hasWidth_treewidth G
    let := d
    apply treewidth_le
    refine ⟨inferInstance, B, T, D.addApices (apexJoin G) (fun h => h), ?_⟩
    intro b
    have := D.apexBag_card (A := A) b
    have := hD b
    change (D.apexBag (A := A) b).card ≤ _
    omega
  · obtain ⟨d, B, T, D, hD⟩ := hasWidth_treewidth (apexJoin (A := A) G)
    let := d
    have hAw := D.apex_card_le_width hD
    have h : HasWidth G (treewidth (apexJoin (A := A) G) - Fintype.card A) :=
      ⟨inferInstance, B, T, D.withoutApices, D.withoutApices_card hD hAw⟩
    have := treewidth_le h
    omega

theorem pathwidth_apexJoin : pathwidth (apexJoin (A := A) G) = pathwidth G + Fintype.card A := by
  classical
  apply le_antisymm
  · obtain ⟨d, r, D, hD⟩ := hasPathWidth_pathwidth G
    let := d
    apply pathwidth_le
    refine ⟨inferInstance, r, D.addApices (apexJoin G) (fun h => h), ?_⟩
    intro b
    have := D.apexBag_card (A := A) b
    have := hD b
    change (D.apexBag (A := A) b).card ≤ _
    omega
  · obtain ⟨d, r, D, hD⟩ := hasPathWidth_pathwidth (apexJoin (A := A) G)
    let := d
    have hAw := D.apex_card_le_width hD
    have h : HasPathWidth G (pathwidth (apexJoin (A := A) G) - Fintype.card A) :=
      ⟨inferInstance, r, D.withoutApices, D.withoutApices_card hD hAw⟩
    have := pathwidth_le h
    omega

end
end TreewidthHom
