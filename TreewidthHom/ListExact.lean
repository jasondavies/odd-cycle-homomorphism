module

public import TreewidthHom.ListMinor
public import TreewidthHom.JoinWidth
public import TreewidthHom.JoinFeedback

@[expose] public section

namespace TreewidthHom
open SimpleGraph

theorem one_le_treewidth_of_adj {V : Type} [Fintype V] {G : SimpleGraph V}
    {u v : V} (huv : G.Adj u v) : 1 ≤ treewidth G := by
  obtain ⟨d, B, T, D, hD⟩ := hasWidth_treewidth G
  let := d
  obtain ⟨b, hu, hv⟩ := D.edge_cover huv
  have hsub : ({u, v} : Finset V) ⊆ D.bag b :=
    Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
  have h := (Finset.card_le_card hsub).trans (hD b)
  rw [Finset.card_pair huv.ne] at h
  omega

namespace OddCycle.ListReduction
variable {m n : ℕ} [Fact (1 < n)]
variable (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))

/-- The join minor yields both width lower bounds, including for nonempty
edgeless inputs. -/
theorem source_width_lower (hn : 5 ≤ n) (hm : 0 < m)
    (hL : ∀ v, ((n - 1 : ℕ) : ZMod n) ∉ L v) :
    treewidth F + 2 ≤ treewidth (source F L) ∧
    pathwidth F + 2 ≤ pathwidth (source F L) := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨M⟩ := join_minor F L hn hL
  constructor
  · simpa only [twoApex, treewidth_apexJoin, Fintype.card_fin] using M.treewidth_le
  · simpa only [twoApex, pathwidth_apexJoin, Fintype.card_fin] using M.pathwidth_le

theorem source_fvs_lower (hn : 5 ≤ n)
    (hL : ∀ v, ((n - 1 : ℕ) : ZMod n) ∉ L v) (hedge : ∃ u v, F.Adj u v) :
    fvs F + 2 ≤ fvs (source F L) := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  obtain ⟨M⟩ := join_minor F L hn hL
  exact (fvs_twoApex_ge F hedge).trans M.fvs_le

/-- The exact structural transfer from the manuscript. Unlike the generic
upper bounds, the lower bounds require the common forbidden last coordinate. -/
theorem exact_parameter_transfer (hn : 5 ≤ n)
    (hL : ∀ v, ((n - 1 : ℕ) : ZMod n) ∉ L v) (hedge : ∃ u v, F.Adj u v) :
    treewidth (source F L) = treewidth F + 2 ∧
    fvs (source F L) = fvs F + 2 ∧
    pathwidth F + 2 ≤ pathwidth (source F L) ∧
    pathwidth (source F L) ≤ pathwidth F + 6 := by
  obtain ⟨u, v, huv⟩ := hedge
  have hm : 0 < m := Nat.zero_lt_of_lt u.isLt
  have hw := source_width_lower F L hn hm hL
  have ht := one_le_treewidth_of_adj huv
  refine ⟨le_antisymm ?_ hw.1, le_antisymm ?_ (source_fvs_lower F L hn hL ⟨u, v, huv⟩),
    hw.2, pathwidth_source_le F L hn⟩
  · have h := treewidth_source_le F L
    simpa only [max_eq_left (by omega : 3 ≤ treewidth F + 2)] using h
  · exact fvs_source_le F L hn

end OddCycle.ListReduction
end TreewidthHom
