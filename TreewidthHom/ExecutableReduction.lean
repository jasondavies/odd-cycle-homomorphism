module
public import TreewidthHom.ExecutableBounds
public import TreewidthHom.SparseArcs
public import TreewidthHom.IndexedAssembly
@[expose] public section
set_option synthInstance.maxSize 1000
namespace TreewidthHom.Executable
open LCSInstance Enumeration

def queryVertices (k N ℓ : ℕ) : Enumeration (QueryVertex k N ℓ) :=
  (sum (fin (k+1)) (sum (prod (fin k) (sum (prod (fin ℓ) (fin (N+1))) unit)) (fin ℓ))).map
    (queryEquiv k N ℓ).symm

def targetVertices {k : ℕ} (words : Fin k → List Bool) : Enumeration (TargetVertex words) :=
  (sum (fin (k+1)) (sum (sigma (fin k) (fun i => fin ((words i).length+1))) bool)).map
    (targetEquiv words).symm

def relationalPresentation {V : Type} [DecidableEq V]
    (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) : Presentation (A.untypedGraph markers) :=
  let iv := incidenceVertices A vs
  let dv := decorated A.typedDag markers iv
  let es := sparseArcs A vs
  assemblyPresentation (A.typedDag.encoded markers).assembly dv es

def relationalGraph {V : Type} [DecidableEq V]
    (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) : EdgeList :=
  indexedAssembly (A.typedDag.encoded markers).assembly
    (decorated A.typedDag markers (incidenceVertices A vs)) (sparseArcs A vs)

def relationalGraphIso {V : Type} [DecidableEq V]
    (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) :
    (relationalGraph A vs).graph ≃g A.untypedGraph markers :=
  indexedAssemblyIso _ _ _

theorem relationalGraph_order {V : Type} [DecidableEq V] [Fintype V]
    (A : Relational (Fin 6) Relational.schemaArity V)
    [∀ r, DecidablePred (A.holds r)] (vs : Enumeration V) :
    (relationalGraph A vs).order = Fintype.card
      (Arrow.AssemblyVertex (A.typedDag.Decorated markers) (A.typedDag.encoded markers).Arc) :=
  (Fintype.card_fin _).symm.trans (Fintype.card_congr (relationalGraphIso A vs).toEquiv)

structure Pair where
  source : EdgeList
  target : EdgeList

def Pair.Accepts (p : Pair) : Prop := Nonempty (p.source.graph →g p.target.graph)
def Pair.WidthBound (p : Pair) (k : ℕ) : Prop :=
  HasWidth p.source.graph (max (2*k) 12) ∧ HasWidth p.target.graph 12

def Pair.SizeBound (p : Pair) (s : ℕ) : Prop :=
  p.source.order ≤ 1000000000000*(s+1)^12 ∧ p.target.order ≤ 1000000000000*(s+1)^12

def raw {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) : Pair :=
  ⟨relationalGraph (query k (totalLength words) ℓ).asRelational (queryVertices k (totalLength words) ℓ),
    relationalGraph (target words).asRelational (targetVertices words)⟩

def yes : Pair := ⟨⟨1,[],by simp⟩,⟨1,[],by simp⟩⟩
def no : Pair := ⟨⟨2,[(0,1)],by decide⟩,⟨1,[],by simp⟩⟩

/-- The executable constructor takes actual finite lists, not an input oracle. -/
def compile (xs : List (List Bool)) (ℓ : ℕ) : Pair :=
  if xs.length = 0 ∨ ℓ = 0 then yes
  else if ∃ i : Fin xs.length, (xs.get i).length < ℓ then no
  else raw xs.get ℓ

theorem raw_correct {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) :
    (raw words ℓ).Accepts ↔ CommonSubsequence words ℓ := by
  rw [show (raw words ℓ).Accepts ↔ Nonempty (
      (query k (totalLength words) ℓ).asRelational.untypedGraph markers →g
      (target words).asRelational.untypedGraph markers) from
    hom_iff_of_iso (relationalGraphIso _ _) (relationalGraphIso _ _)]
  rw [Relational.relationalReduction_iff,← UnaryBinary.hom_iff_relational]
  exact lcs_relational_iff words (word_le_total words)

theorem raw_width {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) : (raw words ℓ).WidthBound k := by
  classical
  constructor
  · apply HasWidth.of_iso (G := (query k (totalLength words) ℓ).asRelational.untypedGraph markers)
      (untyped_width _ ⟨inferInstance,_,_,queryDecomposition _ _ _,query_width _ _ _⟩)
      (relationalGraphIso _ _).symm
  · obtain ⟨B,T,D,h⟩ := target_width words
    have hh := untyped_width (target words) (w := 4) ⟨inferInstance,B,T,D,h⟩
    exact hh.of_iso (relationalGraphIso _ _).symm

theorem presentation_order {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} (p : Presentation G) : p.encode.order = Fintype.card V := by
  exact (Fintype.card_fin _).symm.trans (Fintype.card_congr p.vertices.equiv)

theorem raw_size {k : ℕ} (words : Fin k → List Bool) (ℓ : ℕ) (hℓ : ℓ ≤ dataSize words) :
    (raw words ℓ).SizeBound (dataSize words) := by
  constructor
  · change (relationalGraph _ _).order ≤ _
    rw [relationalGraph_order]
    exact domain_size_bound _ (query_domain_bound words hℓ)
  · change (relationalGraph _ _).order ≤ _
    rw [relationalGraph_order]
    exact domain_size_bound _ (target_domain_bound words)

theorem yes_accepts : yes.Accepts := ⟨SimpleGraph.Hom.id⟩
theorem no_rejects : ¬no.Accepts := by
  rintro ⟨f⟩
  have h := f.map_adj (show no.source.graph.Adj (⟨0,by decide⟩) (⟨1,by decide⟩) by decide)
  rcases h with h | h <;> cases h

theorem compile_correct (xs : List (List Bool)) (ℓ : ℕ) :
    (compile xs ℓ).Accepts ↔ CommonSubsequence xs.get ℓ := by
  unfold compile
  split_ifs with hy hn
  · exact ⟨fun _ => trivial_yes xs.get hy,fun _ => yes_accepts⟩
  · exact ⟨fun h => False.elim (no_rejects h),fun h => False.elim (trivial_no xs.get hn h)⟩
  · exact raw_correct xs.get ℓ

theorem compile_width (xs : List (List Bool)) (ℓ : ℕ) :
    (compile xs ℓ).WidthBound xs.length := by
  unfold compile
  split_ifs
  · constructor <;> apply finite_width <;> change 1 ≤ _ <;> omega
  · constructor <;> apply finite_width
    · change 2 ≤ _; omega
    · change 1 ≤ _; omega
  · exact raw_width xs.get ℓ

theorem compile_size (xs : List (List Bool)) (ℓ : ℕ) :
    (compile xs ℓ).SizeBound (dataSize xs.get) := by
  have hp : 0 < (dataSize xs.get+1)^12 := pow_pos (by omega) _
  unfold compile
  split_ifs with hy hn
  · constructor <;> change 1 ≤ _ <;> omega
  · constructor
    · change 2 ≤ _; omega
    · change 1 ≤ _; omega
  · apply raw_size
    have hk : 0 < xs.length := by omega
    have h1 : ℓ ≤ (xs.get ⟨0,hk⟩).length := by
      by_contra h
      exact hn ⟨⟨0,hk⟩,by omega⟩
    have h2 := word_le_total xs.get ⟨0,hk⟩
    dsimp [dataSize,totalLength] at *
    omega

/-- Correctness, width certificates and polynomial size for the actual executable output. -/
theorem compile_spec (xs : List (List Bool)) (ℓ : ℕ) :
    ((compile xs ℓ).Accepts ↔ CommonSubsequence xs.get ℓ) ∧
    (compile xs ℓ).WidthBound xs.length ∧ (compile xs ℓ).SizeBound (dataSize xs.get) :=
  ⟨compile_correct xs ℓ,compile_width xs ℓ,compile_size xs ℓ⟩

end TreewidthHom.Executable
