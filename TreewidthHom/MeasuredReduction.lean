module
public import TreewidthHom.MeasuredDomains
public import TreewidthHom.MeasuredPreprocessing
public import TreewidthHom.MeasuredRelational
@[expose] public section
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace TreewidthHom.Executable
open LCSInstance EnumRun

abbrev GraphData := ℕ × List (ℕ × ℕ)
def Pair.data (p : Pair) : GraphData × GraphData := (p.source.data,p.target.data)

/-- N is the already computed total input length. Cost q covers each supplied
comparison/access primitive, including recovering the input word count. -/
def rawMeasured {k : ℕ} (words : Fin k → List Bool) (N ℓ q : ℕ) :
    Measured (GraphData × GraphData) :=
  let a := relationalMeasured (query k N ℓ).asRelational
    (EnumRun.queryVertices k N ℓ) (queryHoldsTest k N ℓ q) q
  let b := relationalMeasured (target words).asRelational
    (EnumRun.targetVertices words q) (targetHoldsTest words q) q
  ⟨(a.value,b.value),a.cost+b.cost+q+1⟩

theorem rawMeasured_value {k : ℕ} (words : Fin k → List Bool) (N ℓ q : ℕ)
    (hN : N = totalLength words) : (rawMeasured words N ℓ q).value = (raw words ℓ).data := by
  subst N
  simp only [rawMeasured,relationalMeasured_value]
  rfl

theorem rawMeasured_cost {k N ℓ q s : ℕ} (words : Fin k → List Bool)
    (hk : k ≤ s) (hN : N ≤ s) (hw : ∀ i, (words i).length ≤ s)
    (hℓ : ℓ ≤ s) (hq : q ≤ s+1) (hs : 100 ≤ s) :
    (rawMeasured words N ℓ q).cost ≤ budget 30 s := by
  have heq : q ≤ budget 13 s := hq.trans (budget_mono (show 0 ≤ 13 by omega) s)
  have ha := relationalMeasured_cost (query k N ℓ).asRelational
    (EnumRun.queryVertices k N ℓ) (queryHoldsTest k N ℓ q)
    ((EnumRun.queryVertices_level hk hN hℓ hs).lift (show 9 ≤ 13 by omega)) hs (by omega)
    (queryHoldsTest_level hk hN hℓ hq) heq
  have hb := relationalMeasured_cost (target words).asRelational
    (EnumRun.targetVertices words q) (targetHoldsTest words q)
    ((EnumRun.targetVertices_level words hk hw hq hs).lift (show 6 ≤ 13 by omega)) hs (by omega)
    (targetHoldsTest_level words hk hw hq) heq
  have hq' := heq.trans (budget_mono (show 13 ≤ 29 by omega) s)
  change _ ≤ grow (budget 29 s)
  dsimp only [rawMeasured]
  unfold grow
  nlinarith [sq_nonneg (budget 29 s : ℤ)]

/-- The complete measured constructor uses the preprocessing pass's computed
count, total length and rejection flag. Proofs relating them to the original
input are erased and are never executed as replacement computations. -/
def compileMeasured (xs : List (List Bool)) (ℓ q : ℕ) : Measured (GraphData × GraphData) :=
  let st := statsMeasured q ℓ xs
  if st.value.count = 0 ∨ ℓ = 0 then ⟨yes.data,st.cost+q+3⟩
  else if st.value.short then ⟨no.data,st.cost+q+3⟩
  else
    let r := rawMeasured xs.get st.value.total ℓ q
    ⟨r.value,st.cost+r.cost+q+3⟩

theorem compileMeasured_value (xs : List (List Bool)) (ℓ q : ℕ) :
    (compileMeasured xs ℓ q).value = (compile xs ℓ).data := by
  have hc := (statsMeasured_spec q ℓ xs).1
  have ht := (statsMeasured_spec q ℓ xs).2.1.trans (totalLength_get xs).symm
  have hh := statsMeasured_short q ℓ xs
  unfold compileMeasured compile
  simp only [hc,hh]
  split_ifs
  · rfl
  · rfl
  · exact rawMeasured_value _ _ _ _ ht

/-- Abstract traversal/comparison bound, with the cost of supplied primitives
q left explicit. In particular, a huge requested length is rejected before
constructing any domain whose size depends on its numeric value. -/
theorem compileMeasured_cost (xs : List (List Bool)) (ℓ q s : ℕ)
    (hs : 100 ≤ s) (hk : xs.length ≤ s) (hN : totalLength xs.get ≤ s) (hq : q ≤ s+1) :
    (compileMeasured xs ℓ q).cost ≤ budget 31 s := by
  have hst := statsMeasured_level (ℓ := ℓ) xs hk hN hq
  have hc := (statsMeasured_spec q ℓ xs).1
  have ht := (statsMeasured_spec q ℓ xs).2.1.trans (totalLength_get xs).symm
  have hh := statsMeasured_short q ℓ xs
  have hst' := hst.trans (budget_mono (show 1 ≤ 30 by omega) s)
  have hq' : q ≤ budget 30 s := hq.trans (budget_mono (show 0 ≤ 30 by omega) s)
  unfold compileMeasured
  dsimp only
  split_ifs with hy hn
  · change _ ≤ grow (budget 30 s)
    unfold grow
    nlinarith only [hst',hq',sq_nonneg (budget 30 s : ℤ)]
  · change _ ≤ grow (budget 30 s)
    unfold grow
    nlinarith only [hst',hq',sq_nonneg (budget 30 s : ℤ)]
  · have hpos : 0 < xs.length := by rw [hc] at hy; omega
    have hℓ : ℓ ≤ s := by
      have hnot := mt hh.mpr hn
      have hword : ℓ ≤ (xs.get ⟨0,hpos⟩).length := by
        by_contra h
        exact hnot ⟨⟨0,hpos⟩,by omega⟩
      exact hword.trans ((word_le_total xs.get _).trans hN)
    have hr := rawMeasured_cost xs.get hk (ht ▸ hN)
      (fun i => (word_le_total xs.get i).trans hN) hℓ hq hs
    change _ ≤ grow (budget 30 s)
    unfold grow
    nlinarith only [hst',hq',hr,sq_nonneg (budget 30 s : ℤ)]

/-- Size of an explicit binary input with unary list delimiters and a binary
requested length. The added one covers the representation of zero. -/
def encodedInputSize (xs : List (List Bool)) (ℓ : ℕ) : ℕ :=
  xs.length+(xs.map List.length).sum+ℓ.size+1

/-- A single fixed polynomial bounds the complete measured constructor, for
every input and every supplied primitive-cost budget q. This is deliberately
not a claim about Lean VM or Turing-machine running time. -/
theorem compileMeasured_polynomial : ∃ p : Polynomial ℕ,
    ∀ xs ℓ q, (compileMeasured xs ℓ q).cost ≤ p.eval (100+encodedInputSize xs ℓ+q) := by
  obtain ⟨p,hp⟩ := budget_polynomial 31
  refine ⟨p,fun xs ℓ q => ?_⟩
  rw [← hp]
  apply compileMeasured_cost
  all_goals simp only [encodedInputSize,totalLength_get]; omega

end TreewidthHom.Executable
