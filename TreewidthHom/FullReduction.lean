module

public import TreewidthHom.ReductionSize

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- A finite ordinary graph-homomorphism instance. -/
structure GraphPair where
  Source : Type
  Target : Type
  sourceFinite : Fintype Source
  targetFinite : Fintype Target
  source : SimpleGraph Source
  target : SimpleGraph Target

attribute [instance] GraphPair.sourceFinite GraphPair.targetFinite

def GraphPair.Accepts (P : GraphPair) : Prop := Nonempty (P.source →g P.target)
def GraphPair.WidthBound (P : GraphPair) (k : ℕ) : Prop :=
  HasWidth P.source (max (2*k) 3) ∧ HasWidth P.target 3

def GraphPair.SizeBound (P : GraphPair) (s : ℕ) : Prop :=
  Fintype.card P.Source ≤ 1000000000000*(s+1)^12 ∧
  Fintype.card P.Target ≤ 1000000000000*(s+1)^12

/-- One bag containing the entire finite vertex set. -/
theorem finite_width {V : Type} [Fintype V] (G : SimpleGraph V) {w : ℕ}
    (h : Fintype.card V ≤ w+1) : HasWidth G w := by
  classical
  let D : Decomposition G (⊥ : SimpleGraph Unit) := {
    tree := IsTree.of_subsingleton
    bag := fun _ => Finset.univ
    vertex_cover := fun _ => ⟨(),Finset.mem_univ _⟩
    edge_cover := fun _ => ⟨(),Finset.mem_univ _,Finset.mem_univ _⟩
    running := by
      intro v a b ha hb
      have he : a = b := Subsingleton.elim _ _
      subst b
      exact ⟨.nil,fun _ _ => Finset.mem_univ _⟩ }
  exact ⟨inferInstance,Unit,⊥,D,fun _ => h⟩

def yesPair : GraphPair := ⟨Fin 1,Fin 1,inferInstance,inferInstance,⊥,⊥⟩
def noPair : GraphPair := ⟨Fin 2,Fin 1,inferInstance,inferInstance,⊤,⊥⟩

theorem yesPair_accepts : yesPair.Accepts := ⟨SimpleGraph.Hom.id⟩
theorem noPair_rejects : ¬noPair.Accepts := by
  rintro ⟨f⟩
  have h := f.map_adj (show (⊤ : SimpleGraph (Fin 2)).Adj 0 1 by decide)
  exact h

@[simp] theorem yes_source_card : Fintype.card yesPair.Source = 1 := rfl
@[simp] theorem yes_target_card : Fintype.card yesPair.Target = 1 := rfl
@[simp] theorem no_source_card : Fintype.card noPair.Source = 2 := rfl
@[simp] theorem no_target_card : Fintype.card noPair.Target = 1 := rfl

theorem trivial_width (k : ℕ) : yesPair.WidthBound k ∧ noPair.WidthBound k := by
  constructor <;> constructor <;> apply finite_width <;>
    simp only [yes_source_card,yes_target_card,no_source_card,no_target_card] <;> omega

theorem trivial_size (s : ℕ) : yesPair.SizeBound s ∧ noPair.SizeBound s := by
  have h : 0 < (s+1)^12 := pow_pos (by omega) _
  constructor <;> constructor <;>
    simp only [yes_source_card,yes_target_card,no_source_card,no_target_card] <;> omega

namespace LCSInstance

noncomputable def rawPair {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) : GraphPair :=
  ⟨_,_,inferInstance,inferInstance,sourceGraph k (totalLength words) ℓ,targetGraph words⟩

/-- Only lengths are tested during preprocessing; LCS itself is never decided here. -/
noncomputable def reduce {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) : GraphPair :=
  if k = 0 ∨ ℓ = 0 then yesPair
  else if ∃ i, (words i).length < ℓ then noPair
  else rawPair words ℓ

theorem trivial_yes {k ℓ : ℕ} (words : Fin k → List Bool) (h : k = 0 ∨ ℓ = 0) :
    CommonSubsequence words ℓ := by
  rcases h with h | rfl
  · subst k
    exact ⟨List.replicate ℓ false,by simp,fun i => Fin.elim0 i⟩
  · exact ⟨[],rfl,fun _ => List.nil_sublist _⟩

theorem trivial_no {k ℓ : ℕ} (words : Fin k → List Bool)
    (h : ∃ i, (words i).length < ℓ) : ¬CommonSubsequence words ℓ := by
  obtain ⟨i,hi⟩ := h
  rintro ⟨z,hz,hs⟩
  have hh := (hs i).length_le
  omega

/-- Correctness for every binary LCS instance, including all preprocessing branches. -/
theorem reduce_correct {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) :
    (reduce words ℓ).Accepts ↔ CommonSubsequence words ℓ := by
  classical
  unfold reduce
  split_ifs with hyes hno
  · exact ⟨fun _ => trivial_yes words hyes,fun _ => yesPair_accepts⟩
  · exact ⟨fun h => False.elim (noPair_rejects h),fun h => False.elim (trivial_no words hno h)⟩
  · exact lcs_graph_iff words (word_le_total words)

theorem reduce_width {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) :
    (reduce words ℓ).WidthBound k := by
  classical
  unfold reduce
  split_ifs
  · exact (trivial_width k).1
  · exact (trivial_width k).2
  · exact ⟨source_width k _ ℓ,final_target_width words⟩

/-- Polynomial output size in word data alone, even when the requested length
is supplied in binary and is much larger than all input words. -/
theorem reduce_size {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) :
    (reduce words ℓ).SizeBound (dataSize words) := by
  classical
  unfold reduce
  split_ifs with hyes hno
  · exact (trivial_size _).1
  · exact (trivial_size _).2
  · have hk : 0 < k := by omega
    have hℓ : ℓ ≤ dataSize words := by
      have h1 : ℓ ≤ (words ⟨0,hk⟩).length := by
        by_contra h
        exact hno ⟨⟨0,hk⟩,by omega⟩
      have h2 := word_le_total words ⟨0,hk⟩
      dsimp [dataSize,totalLength] at *
      omega
    exact ⟨graph_bound_of_domain _ (query_domain_bound words hℓ),
      graph_bound_of_domain _ (target_domain_bound words)⟩

/-- The full combinatorial reduction: decision equivalence, parameter bound,
constant target width, and finite polynomial output size, with no input promises. -/
theorem full_reduction {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) :
    ((reduce words ℓ).Accepts ↔ CommonSubsequence words ℓ) ∧
    (reduce words ℓ).WidthBound k ∧ (reduce words ℓ).SizeBound (dataSize words) :=
  ⟨reduce_correct words ℓ,reduce_width words ℓ,reduce_size words ℓ⟩

end LCSInstance
end TreewidthHom
