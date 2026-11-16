module

public import TreewidthHom.ListTheorem
public import TreewidthHom.ListSparse

@[expose] public section

/-!
# Treewidth, pathwidth and feedback vertex number as numbers

The main theorem transfers decomposition certificates. Here the three parameters
are defined as minima, and the transfer is restated as inequalities between them.
The minima are attained for finite graphs; for a graph with no decomposition the
value is the default `0`.
-/
namespace TreewidthHom
open SimpleGraph

/-- The least width of a tree decomposition. -/
noncomputable def treewidth {V : Type} (G : SimpleGraph V) : ℕ := sInf {w | HasWidth G w}

/-- The least width of a path decomposition. -/
noncomputable def pathwidth {V : Type} (G : SimpleGraph V) : ℕ := sInf {w | HasPathWidth G w}

/-- The least size of a set of vertices whose deletion leaves an acyclic graph. -/
noncomputable def fvs {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ (G.induce {v | v ∉ S}).IsAcyclic}

section
variable {V : Type} (G : SimpleGraph V)

/-- One bag containing every vertex. -/
theorem hasPathWidth_card [Fintype V] : HasPathWidth G (Fintype.card V) := by
  classical
  let D : Decomposition G (pathGraph (0+1)) :=
    intervalDecomposition G 0 (fun _ => Finset.univ)
      (fun _ => ⟨0,Finset.mem_univ _⟩)
      (fun _ => ⟨0,Finset.mem_univ _,Finset.mem_univ _⟩)
      (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _)
  exact ⟨inferInstance,0,D,fun _ => Nat.le_succ _⟩

theorem hasPathWidth_pathwidth [Fintype V] : HasPathWidth G (pathwidth G) :=
  Nat.sInf_mem (s := {w | HasPathWidth G w}) ⟨_,hasPathWidth_card G⟩

theorem hasWidth_treewidth [Fintype V] : HasWidth G (treewidth G) :=
  Nat.sInf_mem (s := {w | HasWidth G w}) ⟨_,(hasPathWidth_card G).hasWidth⟩

variable {G}

theorem treewidth_le {w : ℕ} (h : HasWidth G w) : treewidth G ≤ w := Nat.sInf_le h

theorem pathwidth_le {w : ℕ} (h : HasPathWidth G w) : pathwidth G ≤ w := Nat.sInf_le h

theorem fvs_le (S : Finset V) (h : (G.induce {v | v ∉ S}).IsAcyclic) : fvs G ≤ S.card :=
  Nat.sInf_le ⟨S,rfl,h⟩

variable (G)

theorem treewidth_le_pathwidth [Fintype V] : treewidth G ≤ pathwidth G :=
  treewidth_le (hasPathWidth_pathwidth G).hasWidth

/-- A minimum feedback vertex set exists. -/
theorem exists_fvs [Fintype V] :
    ∃ S : Finset V, S.card = fvs G ∧ (G.induce {v | v ∉ S}).IsAcyclic := by
  have h : fvs G ∈ {k | ∃ S : Finset V, S.card = k ∧ (G.induce {v | v ∉ S}).IsAcyclic} := by
    apply Nat.sInf_mem
    refine ⟨_,Finset.univ,rfl,?_⟩
    intro x
    exact absurd (Finset.mem_univ x.val) x.prop
  exact h

end

namespace OddCycle.ListReduction
variable {m n : ℕ} [Fact (1 < n)]

/-- The reduction raises treewidth by at most two, above a floor of four. -/
theorem treewidth_source_le (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :
    treewidth (source F L) ≤ max (treewidth F + 2) 4 :=
  treewidth_le (source_width F L (hasWidth_treewidth F))

/-- The reduction raises pathwidth by at most six. -/
theorem pathwidth_source_le (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hn : 5 ≤ n) : pathwidth (source F L) ≤ pathwidth F + 6 :=
  pathwidth_le (source_pathWidth F L hn (hasPathWidth_pathwidth F))

theorem pathwidth_target_le (hn : 3 ≤ n) : pathwidth (cyc n) ≤ 2 :=
  pathwidth_le (target_pathWidth n hn)

/-- The reduction raises the feedback vertex number by at most two. -/
theorem fvs_source_le (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hn : 5 ≤ n) : fvs (source F L) ≤ fvs F + 2 := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  obtain ⟨S,hS,hacyc⟩ := exists_fvs F
  let S' : Finset (SourceVertex F L) := Finset.univ.filter (fun v => removed S v)
  have hset : {v : SourceVertex F L | v ∉ S'} = {v | ¬ removed S v} := by
    ext v
    simp [S']
  have h1 : ((source F L).induce {v | v ∉ S'}).IsAcyclic := by
    rw [hset]
    exact source_feedback F L S hn hacyc
  have hcard : S'.card = S.card + 2 := by
    rw [← removed_card F L S,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have h2 := fvs_le S' h1
  omega

/-- The source has at most twice as many edges as vertices. -/
theorem source_edges_le (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :
    Nat.card (source F L).edgeSet ≤ 2*Nat.card (SourceVertex F L) := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  exact (source_degenerate F L).card_edgeSet_le

/-- The reduction stated for the parameters themselves, together with the
sparsity of the source. Complexity classes are not encoded here. -/
theorem parameter_reduction (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) :
    (Nonempty (source F L →g cyc n) ↔ Colorable F L) ∧
    treewidth (source F L) ≤ max (treewidth F + 2) 4 ∧
    pathwidth (source F L) ≤ pathwidth F + 6 ∧
    fvs (source F L) ≤ fvs F + 2 ∧
    pathwidth (cyc n) ≤ 2 ∧
    IsDegenerate (source F L) 2 ∧
    (n : ℕ∞) ≤ (source F L).egirth ∧
    ((∀ v, ∃ d, d ∉ L v) → (source F L).Connected) ∧
    Nat.card (SourceVertex F L) ≤ 2+m+m*n*n+(m*n+m*m)*n ∧
    Nat.card (source F L).edgeSet ≤ 2*Nat.card (SourceVertex F L) :=
  ⟨source_hom_iff_colorable F L hodd hn,treewidth_source_le F L,pathwidth_source_le F L hn,
    fvs_source_le F L hn,pathwidth_target_le (by omega),source_degenerate F L,
    source_le_egirth F L hn,source_connected F L hn,source_card_le F L,source_edges_le F L⟩

end OddCycle.ListReduction
end TreewidthHom
