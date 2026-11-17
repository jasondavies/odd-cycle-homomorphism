module

public import TreewidthHom

@[expose] public section

/-!
# Proved Palomar statement

The statement is deliberately identical to `Challenge.lean`, which is compiled
independently. The existential graph is the concrete construction already proved
in this repository; all structural properties refer to this same witness.
-/

namespace TreewidthHom
open SimpleGraph OddCycle OddCycle.ListReduction

/-- Every finite List Colouring instance over an odd residue palette has an
ordinary graph-homomorphism encoding with additive structural overhead.
The same witness satisfies both certificate transfers and numerical bounds.
`egirth` is the length of a shortest cycle, or infinity for a forest.
The connectedness premise holds for padded palettes; exact girth needs a
nonempty input. The polynomial bound counts vertices, not machine resources. -/
theorem Palomar.list_elimination {m n : ℕ} (F : SimpleGraph (Fin m))
    (L : Fin m → Finset (ZMod n)) (hodd : Odd n) (hn : 5 ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod n))) ↔
        ∃ c : Fin m → ZMod n, (∀ v, c v ∈ L v) ∧
          ∀ u v, F.Adj u v → c u ≠ c v) ∧
      (∀ w, HasWidth F w → HasWidth G (max (w+2) 3)) ∧
      (∀ p, HasPathWidth F p → HasPathWidth G (p+6)) ∧
      HasPathWidth (circulantGraph {1} : SimpleGraph (ZMod n)) 2 ∧
      (∀ S : Finset (Fin m), (F.induce {v | v ∉ S}).IsAcyclic →
        ∃ S' : Finset V, S'.card = S.card+2 ∧
          (G.induce {v | v ∉ S'}).IsAcyclic) ∧
      treewidth G ≤ max (treewidth F + 2) 3 ∧
      pathwidth G ≤ pathwidth F + 6 ∧
      fvs G ≤ fvs F + 2 ∧
      IsDegenerate G 2 ∧
      (n : ℕ∞) ≤ G.egirth ∧
      (0 < m → G.egirth = n) ∧
      ((∀ v, ∃ d, d ∉ L v) → G.Connected) ∧
      Nat.card V ≤ 2+m+m*n*n+(m*n+m*m)*n ∧
      Nat.card G.edgeSet ≤ 2*Nat.card V ∧
      ((∀ v, ((n-1 : ℕ) : ZMod n) ∉ L v) →
        (0 < m → treewidth F + 2 ≤ treewidth G ∧ pathwidth F + 2 ≤ pathwidth G) ∧
        ((∃ u v, F.Adj u v) → treewidth G = treewidth F + 2 ∧ fvs G = fvs F + 2)) ∧
      (∀ k, 5 ≤ k →
        (Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod k))) ↔
          Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod (min k (2*Fintype.card V+5))))))) ∧
      (0 < m →
        ((∃ k, 3 ≤ k ∧ Odd k ∧
          Nonempty (G →g (circulantGraph {1} : SimpleGraph (ZMod k))) ∧
          Nonempty ((circulantGraph {1} : SimpleGraph (ZMod k)) →g G)) ↔
        ∃ c : Fin m → ZMod n, (∀ v, c v ∈ L v) ∧
          ∀ u v, F.Adj u v → c u ≠ c v)) := by
  classical
  let : Fact (1 < n) := ⟨by omega⟩
  let : Fintype (Link F L) := Subtype.fintype _
  refine ⟨SourceVertex F L, inferInstance, source F L,
    source_hom_iff_colorable F L hodd hn,
    fun _ hw => source_width F L hw,
    fun _ hp => source_pathWidth F L hn hp,
    target_pathWidth n (by omega), ?_,
    treewidth_source_le F L, pathwidth_source_le F L hn, fvs_source_le F L hn,
    source_degenerate F L, source_le_egirth F L hn, source_egirth F L hn,
    source_connected F L hn, source_card_le F L, source_edges_le F L, ?_, ?_,
    source_hasOddCycleCore_iff F L hodd hn⟩
  · intro S hS
    let S' : Finset (SourceVertex F L) := Finset.univ.filter (fun v => removed S v)
    have hset : {v : SourceVertex F L | v ∉ S'} = {v | ¬ removed S v} := by
      ext v
      simp [S']
    refine ⟨S', ?_, ?_⟩
    · rw [← removed_card F L S, Nat.card_eq_fintype_card, Fintype.card_subtype]
    · rw [hset]
      exact source_feedback F L S hn hS
  · intro hL
    refine ⟨fun hm => source_width_lower F L hn hm hL, ?_⟩
    intro hedge
    have h := exact_parameter_transfer F L hn hL hedge
    exact ⟨h.1, h.2.1⟩
  · intro k hk
    let : Fact (1 < k) := ⟨by omega⟩
    exact hom_iff_capped hk

end TreewidthHom
