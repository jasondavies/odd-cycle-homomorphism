module

public import TreewidthHom.WeightedFormula
public import TreewidthHom.OddCycleCore
public import TreewidthHom.Parameters

@[expose] public section

namespace TreewidthHom.WeightedFormula.Formula
open SimpleGraph OddCycle OddCycle.ListReduction
noncomputable section

variable {P X : Type} [Fintype P] [Fintype X] (F : Formula P X)

/-- Exact-weight satisfiability over the whole variable universe, including
variables with no occurrence in the formula. -/
def Satisfiable (k : ℕ) := ∃ U : Finset X, U.card = k ∧ F.eval (U : Set X) (.inl ())

omit [Fintype X] in
theorem satisfiable_iff_proper (k : ℕ) :
    F.Satisfiable k ↔ ∃ c : Vertex k P → Colour P X, F.Proper c := by
  classical
  constructor
  · rintro ⟨U,hU,h⟩
    let e := (U.equivFinOfCardEq hU).symm
    let s := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ U))
    have hr : Set.range s = (U : Set X) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact (e i).property
      · intro hx
        exact ⟨e.symm ⟨x,hx⟩, by simp [s]⟩
    obtain ⟨c,hc,_⟩ := (F.extends_iff s).2 (hr ▸ h)
    exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩
    have pick (i : Fin k) : ∃ x, c (.inl i) = .inl x := hc.1 (.inl i)
    choose s hs using pick
    have hinj : Function.Injective s := by
      intro i j he
      by_contra h
      exact hc.2 _ _ (show (F.graph k).Adj (.inl i) (.inl j) from h)
        (by rw [hs i, hs j, he])
    let e : Fin k ↪ X := ⟨s,hinj⟩
    refine ⟨Finset.univ.map e, by simp, ?_⟩
    simpa using (F.extends_iff e).1 ⟨c,hc,hs⟩

/-- Vertex numbering for the existing List Colouring construction. -/
abbrev order (P : Type) [Fintype P] (k : ℕ) := Fintype.card (Vertex k P)

def numberedGraph (k : ℕ) : SimpleGraph (Fin (order P k)) :=
  (F.graph k).comap (Fintype.equivFin (Vertex k P)).symm

def selectors (P : Type) [Fintype P] (k : ℕ) : Finset (Fin (order P k)) :=
  Finset.univ.map (Function.Embedding.inl.trans (Fintype.equivFin (Vertex k P)).toEmbedding)

omit [Fintype X] in
theorem selectors_tree (k : ℕ) :
    (selectors P k).card = k ∧
    ((F.numberedGraph k).induce {v | v ∉ selectors P k}).IsTree := by
  classical
  refine ⟨by simp [selectors], ?_⟩
  let e := Fintype.equivFin (Vertex k P)
  have keep (v : Node P) : e (.inr v) ∉ selectors P k := by simp [selectors,e]
  let f (v : Node P) : {i | i ∉ selectors P k} := ⟨e (.inr v),keep v⟩
  have bij : Function.Bijective f := by
    constructor
    · intro u v h
      exact Sum.inr.inj (e.injective (congrArg Subtype.val h))
    · rintro ⟨i,hi⟩
      cases h : e.symm i with
      | inl j =>
        exact (hi (Finset.mem_map.mpr ⟨j,Finset.mem_univ _, by
          change e (.inl j) = i
          simp [← h]⟩)).elim
      | inr v =>
        exact ⟨v, Subtype.ext (by change e (.inr v) = i; simp [← h])⟩
  let iso : F.tree ≃g (F.numberedGraph k).induce {i | i ∉ selectors P k} :=
    { toEquiv := Equiv.ofBijective f bij
      map_rel_iff' := by
        intro u v
        change (F.graph k).Adj (e.symm (e (.inr u))) (e.symm (e (.inr v))) ↔ _
        simp only [Equiv.symm_apply_apply]
        rfl }
  apply iso.isTree_iff.mp
  apply F.toGraft.isTree
  exact ⟨⟨by rintro ⟨⟩ ⟨⟩; exact Reachable.refl _⟩, isAcyclic_bot⟩

/-- A single odd target long enough for the colours and the cube-root girth bound.
Unused gate-colour codes are harmless. -/
def length (P X : Type) [Fintype P] [Fintype X] (k : ℕ) :=
  2 * (Fintype.card (Colour P X) + order P k) + 5

instance length_fact (k : ℕ) : Fact (1 < length P X k) := ⟨by unfold length; omega⟩

def residueEmbedding (k : ℕ) : Colour P X ↪ ZMod (length P X k) :=
  (Fintype.equivFin (Colour P X)).toEmbedding.trans
    (Fin.castLEEmb (m := length P X k) (by unfold length; omega))

def residueLists (k : ℕ) (i : Fin (order P k)) : Finset (ZMod (length P X k)) := by
  classical
  exact (Finset.univ.filter (F.domain ((Fintype.equivFin (Vertex k P)).symm i))).map
    (residueEmbedding (P := P) (X := X) k)

theorem satisfiable_iff_colorable (k : ℕ) :
    F.Satisfiable k ↔ Colorable (F.numberedGraph k) (F.residueLists k) := by
  classical
  rw [F.satisfiable_iff_proper]
  let e := Fintype.equivFin (Vertex k P)
  let a := residueEmbedding (P := P) (X := X) k
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨fun i => a (c (e.symm i)), fun i => Finset.mem_map.mpr
      ⟨c (e.symm i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc.1 _⟩,rfl⟩,?_⟩
    intro i j h
    exact fun eq => hc.2 _ _ h (a.injective eq)
  · rintro ⟨d,hL,hd⟩
    have pre (v : Vertex k P) : ∃ b, F.domain v b ∧ a b = d (e v) := by
      obtain ⟨b,hb,eq⟩ := Finset.mem_map.mp (hL (e v))
      refine ⟨b,?_,eq⟩
      simpa [e] using (Finset.mem_filter.mp hb).2
    choose c hc eq using pre
    refine ⟨c,hc,?_⟩
    intro u v h he
    apply hd (e u) (e v) _ (by rw [← eq u, ← eq v, he])
    change (F.graph k).Adj (e.symm (e u)) (e.symm (e v))
    simpa using h

/-- One concrete output answers both cycle questions. The witness feedback set
consists of the selector hubs and the two anchors. -/
theorem cycle_reduction (k : ℕ) :
    let G := source (F.numberedGraph k) (F.residueLists k)
    let n := length P X k
    Odd n ∧ 5 ≤ n ∧
    (F.Satisfiable k ↔ Nonempty (G →g cyc n)) ∧
    (F.Satisfiable k ↔ HasOddCycleCore G) ∧
    (∃ S : Finset _, S.card = k+2 ∧ (G.induce {v | v ∉ S}).IsAcyclic) ∧
    G.egirth = n ∧
      Nat.card (SourceVertex (F.numberedGraph k) (F.residueLists k)) ≤ 4*n^3 := by
  classical
  let n := length P X k
  have hn : 5 ≤ n := by dsimp [n,length]; omega
  have hodd : Odd n := ⟨Fintype.card (Colour P X) + order P k + 2, by dsimp [n,length]; omega⟩
  have hm : 0 < order P k := Fintype.card_pos_iff.mpr ⟨.inr (.inl ())⟩
  have hmn : order P k ≤ n := by dsimp only [n,length]; omega
  let H := F.numberedGraph k
  let L := F.residueLists k
  have he := F.satisfiable_iff_colorable k
  obtain ⟨hg,hcard⟩ := source_girth_and_card H L hn hm hmn
  refine ⟨hodd, hn, he.trans (source_hom_iff_colorable H L hodd hn).symm,
    he.trans (source_hasOddCycleCore_iff H L hodd hn hm).symm, ?_, hg, hcard⟩
  let S := selectors P k
  obtain ⟨hs,ht⟩ := F.selectors_tree k
  let T : Finset (SourceVertex H L) := Finset.univ.filter (removed S)
  have hset : {v | v ∉ T} = {v : SourceVertex H L | ¬ removed S v} := by ext; simp [T]
  refine ⟨T, ?_, hset ▸ source_feedback H L S hn ht.isAcyclic⟩
  have hc := removed_card H L S
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  exact hc.trans (congrArg (· + 2) hs)

end
end TreewidthHom.WeightedFormula.Formula
