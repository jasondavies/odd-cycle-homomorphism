module

public import TreewidthHom.Join

@[expose] public section

namespace TreewidthHom
open SimpleGraph
variable {V : Type} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
private theorem fvs_lt_vertexCover (C : Finset V) (hC : C.Nonempty)
    (hcover : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) : fvs G + 1 ≤ C.card := by
  classical
  obtain ⟨c, hc⟩ := hC
  let S := C.erase c
  have ha : (G.induce {v | v ∉ S}).IsAcyclic := by
    let f : G.induce {v | v ∉ S} →g starGraph c :=
      { toFun := Subtype.val
        map_rel' := by
          intro u v huv
          apply starGraph_adj.mpr
          refine ⟨(show G.Adj u.val v.val from huv).ne, ?_⟩
          rcases hcover u.val v.val huv with hu | hv
          · exact Or.inl (by have := u.property; simp only [S, Finset.mem_erase, not_and] at this; by_contra h; exact this h hu)
          · exact Or.inr (by have := v.property; simp only [S, Finset.mem_erase, not_and] at this; by_contra h; exact this h hv) }
    exact (isAcyclic_starGraph c).comap f Subtype.val_injective
  have hk := fvs_le S ha
  have hcard : S.card + 1 = C.card := by simpa [S] using Finset.card_erase_add_one hc
  omega

private theorem fvs_add_two_le_card {u v : V} (huv : u ≠ v) : fvs G + 2 ≤ Fintype.card V := by
  classical
  let S := (Finset.univ : Finset V) \ {u, v}
  have ha : (G.induce {x | x ∉ S}).IsAcyclic := by
    have mem : ∀ x : {x | x ∉ S}, x.val = u ∨ x.val = v := by
      intro x
      have hx := x.property
      simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, Finset.mem_insert, Finset.mem_singleton] at hx
      exact hx
    let f : G.induce {x | x ∉ S} →g starGraph u :=
      { toFun := Subtype.val
        map_rel' := by
          intro x y hxy
          have hne := (show G.Adj x.val y.val from hxy).ne
          apply starGraph_adj.mpr
          refine ⟨hne, ?_⟩
          rcases mem x with hx | hx
          · exact Or.inl hx
          · rcases mem y with hy | hy
            · exact Or.inr hy
            · exact (hne (hx.trans hy.symm)).elim }
    exact (isAcyclic_starGraph u).comap f Subtype.val_injective
  have hk := fvs_le S ha
  have hcard : S.card + 2 = Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (t := (Finset.univ : Finset V))
      (show ({u, v} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)
    simpa [S, huv] using h
  omega

/-- Deleting a feedback set from the join costs two more vertices than from the
input, provided the input contains an edge. -/
theorem fvs_twoApex_ge (hedge : ∃ u v, G.Adj u v) : fvs G + 2 ≤ fvs (twoApex G) := by
  classical
  obtain ⟨S, hcard, hS⟩ := exists_fvs (twoApex G)
  let C := S.toLeft
  have hsum : C.card + S.toRight.card = S.card := S.card_toLeft_add_card_toRight
  have no_triangle : ∀ a b c : {x : V ⊕ Fin 2 | x ∉ S},
      (twoApex G).Adj a.val b.val → (twoApex G).Adj a.val c.val →
      (twoApex G).Adj b.val c.val → False := by
    intro a b c hab hac hbc
    exact hS.cliqueFree_three {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  by_cases hall : ∀ a : Fin 2, Sum.inr a ∈ S
  · have ha : (G.induce {v | v ∉ C}).IsAcyclic := by
      let f : G.induce {v | v ∉ C} →g (twoApex G).induce {x | x ∉ S} :=
        { toFun := fun v => ⟨.inl v.val, by simpa [C] using v.property⟩
          map_rel' := fun h => h }
      exact hS.comap f (fun u v h => Subtype.ext (Sum.inl.inj (congrArg Subtype.val h)))
    have hk := fvs_le C ha
    have hr : S.toRight = (Finset.univ : Finset (Fin 2)) := by ext a; simp [hall a]
    have : S.toRight.card = 2 := by rw [hr]; simp
    omega
  · simp only [not_forall] at hall
    obtain ⟨a, ha⟩ := hall
    have cover : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := by
      intro u v huv
      by_contra h
      have hu : Sum.inl u ∉ S := by simpa [C] using (not_or.mp h).1
      have hv : Sum.inl v ∉ S := by simpa [C] using (not_or.mp h).2
      exact no_triangle ⟨.inr a, ha⟩ ⟨.inl u, hu⟩ ⟨.inl v, hv⟩ trivial trivial huv
    obtain ⟨u, v, huv⟩ := hedge
    have hC : C.Nonempty := (cover u v huv).elim (fun h => ⟨u, h⟩) (fun h => ⟨v, h⟩)
    have hk := fvs_lt_vertexCover G C hC cover
    by_cases hr : S.toRight.Nonempty
    · have := Finset.card_pos.mpr hr
      omega
    · have hempty : S.toRight = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
      have h0 : Sum.inr (0 : Fin 2) ∉ S := by simpa using (show (0 : Fin 2) ∉ S.toRight by rw [hempty]; simp)
      have h1 : Sum.inr (1 : Fin 2) ∉ S := by simpa using (show (1 : Fin 2) ∉ S.toRight by rw [hempty]; simp)
      have hfull : C = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro w
        by_contra hw
        have hw' : Sum.inl w ∉ S := by simpa [C] using hw
        exact no_triangle ⟨.inr 0, h0⟩ ⟨.inr 1, h1⟩ ⟨.inl w, hw'⟩ (show (0 : Fin 2) ≠ 1 from by decide) trivial trivial
      have hbound := fvs_add_two_le_card G huv.ne
      have : C.card = Fintype.card V := by rw [hfull]; simp
      omega

end TreewidthHom
