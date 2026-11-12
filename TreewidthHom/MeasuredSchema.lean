module
public import TreewidthHom.IndexedAssemblyCost
public import TreewidthHom.MeasuredDecision
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace TreewidthHom.Executable
namespace EnumRun
variable {α β : Type*}

/-- Feed the actually computed list into the next stage. -/
def output {e : Enumeration α} (a : EnumRun e) : Enumeration α where
  elems := a.run.value
  nodup := by rw [a.correct]; exact e.nodup
  complete x := by rw [a.correct]; exact e.complete x

theorem output_eq {e : Enumeration α} (a : EnumRun e) : a.output = e := by
  cases e with | mk xs hn hc =>
    cases a with | mk r h =>
      cases r with | mk ys c =>
        dsimp at h
        subst ys
        rfl

def mapInto {e : Enumeration α} (a : EnumRun e) (out : Enumeration β) (f : α → β)
    (h : out.elems = e.elems.map f) : EnumRun out where
  run := let b := Measured.mapList (fun x => Measured.step (f x)) a.run.value
         ⟨b.value,a.run.cost+b.cost+1⟩
  correct := by simp [Measured.mapList_value,Measured.step,a.correct,h]

theorem bounded_mapInto {e : Enumeration α} {a : EnumRun e} {b : ℕ} (ha : a.Bounded b)
    (out : Enumeration β) (f : α → β) (h : out.elems = e.elems.map f) :
    (a.mapInto out f h).Bounded (grow b) := by
  have hm := Measured.mapList_cost (fun x => Measured.step (f x)) a.run.value
    (c := 1) (by intro _ _; exact le_rfl)
  rw [a.correct] at hm
  have h1 := ha.1; have h2 := ha.2
  constructor
  · rw [h,List.length_map]
    exact h1.trans (le_grow b)
  · change a.run.cost+(Measured.mapList (fun x => Measured.step (f x)) a.run.value).cost+1 ≤ _
    rw [a.correct]
    unfold grow
    nlinarith [sq_nonneg (b : ℤ)]

def functions {e : Enumeration α} (a : EnumRun e) : (n : ℕ) → EnumRun (Executable.functions e n)
  | 0 => ⟨⟨[Fin.elim0],2⟩,rfl⟩
  | n+1 => (a.prod (functions a n)).map (finFunSucc α n).symm

abbrev Level {e : Enumeration α} (a : EnumRun e) (d s : ℕ) := a.Bounded (budget d s)

theorem Level.lift {e : Enumeration α} {a : EnumRun e} {d d' s : ℕ}
    (h : a.Level d s) (hd : d ≤ d') : a.Level d' s := h.mono (budget_mono hd s)

theorem level_map {e : Enumeration α} {a : EnumRun e} {d s : ℕ} (h : a.Level d s)
    (f : α ≃ β) : (a.map f).Level (d+1) s := bounded_map h f

theorem level_sum {e : Enumeration α} {f : Enumeration β} {a : EnumRun e} {b : EnumRun f}
    {d s : ℕ} (ha : a.Level d s) (hb : b.Level d s) : (a.sum b).Level (d+1) s := bounded_sum ha hb

theorem level_prod {e : Enumeration α} {f : Enumeration β} {a : EnumRun e} {b : EnumRun f}
    {d s : ℕ} (ha : a.Level d s) (hb : b.Level d s) : (a.prod b).Level (d+2) s := bounded_prod ha hb

theorem level_sigma {ι : Type*} {δ : ι → Type*} {e : Enumeration ι} {f : ∀ i, Enumeration (δ i)}
    {a : EnumRun e} {b : ∀ i, EnumRun (f i)} {d s : ℕ}
    (ha : a.Level d s) (hb : ∀ i, (b i).Level d s) : (sigma a b).Level (d+1) s := bounded_sigma ha hb

theorem level_fin {n s : ℕ} (hn : n ≤ s+1) : (fin n).Level 1 s := bounded_fin hn

theorem level_unit {s : ℕ} (hs : 2 ≤ s+1) : unit.Level 0 s := ⟨by simp [budget],hs⟩
theorem level_bool {s : ℕ} (hs : 3 ≤ s+1) : bool.Level 0 s := ⟨by simpa [budget] using (show 2 ≤ s+1 by omega),hs⟩

theorem functions_level {e : Enumeration α} {a : EnumRun e} {d s : ℕ}
    (ha : a.Level d s) (hs : 2 ≤ s+1) (n : ℕ) : (a.functions n).Level (d+3*n) s := by
  induction n with
  | zero =>
    have hb : 2 ≤ budget d s := hs.trans (budget_mono (Nat.zero_le d) s)
    change 1 ≤ budget d s ∧ 2 ≤ budget d s
    exact ⟨by omega,hb⟩
  | succ n ih =>
    have h := level_map (level_prod (ha.lift (by omega)) ih) (finFunSucc α n).symm
    simpa only [functions,Executable.functions,show d+3*n+2+1 = d+3*(n+1) by omega] using h

end EnumRun

namespace SchemaRun
open EnumRun
variable {V : Type} (A : Relational (Fin 6) Relational.schemaArity V)
variable [∀ r, DecidablePred (A.holds r)] {vs : Enumeration V}
variable (a : EnumRun vs) (test : ∀ r t, Measured (Decidable (A.holds r t)))

def facts : EnumRun (Executable.facts A vs) :=
  sigma (fin 6) (fun r => (a.functions (Relational.schemaArity r)).subtype (A.holds r) (test r))

def incidence : EnumRun (incidenceVertices A vs) :=
  (a.sum (sigma (facts A a test) (fun f => unit.sum (fin (Relational.schemaArity f.1))))).map A.vertexEquiv.symm

def cycles : EnumRun (decorated A.typedDag markers (incidenceVertices A vs)) :=
  sigma (incidence A a test) (fun v => (fin (markers.length (A.tag v))).map (ZMod.finEquiv _).toEquiv)

def arcs : EnumRun (sparseArcs A vs) :=
  let codes := (cycles A a test).sum (bool.prod (sigma (facts A a test) (fun f => fin (Relational.schemaArity f.1))))
  codes.mapInto (sparseArcs A vs) (arcOfCode A) rfl

theorem facts_level {d s : ℕ} (ha : a.Level d s) (hs : 100 ≤ s) (hd : 1 ≤ d)
    (ht : ∀ r t, (test r t).cost ≤ budget d s) : (facts A a test).Level (d+8) s := by
  have hf : (fin 6).Level (d+7) s := (level_fin (by omega : 6 ≤ s+1)).lift (by omega)
  apply level_sigma hf
  intro r
  have hr : Relational.schemaArity r ≤ 2 := by unfold Relational.schemaArity; split <;> omega
  have hh := (functions_level ha (by omega) (Relational.schemaArity r)).lift
    (show d+3*Relational.schemaArity r ≤ d+6 by omega)
  exact bounded_subtype hh _ (test r) (fun t => (ht r t).trans (budget_mono (by omega) s))

theorem incidence_level {d s : ℕ} (ha : a.Level d s) (hs : 100 ≤ s) (hd : 1 ≤ d)
    (ht : ∀ r t, (test r t).cost ≤ budget d s) : (incidence A a test).Level (d+11) s := by
  have hf := facts_level A a test ha hs hd ht
  have hp : ∀ f : A.Fact, (unit.sum (fin (Relational.schemaArity f.1))).Level (d+8) s := by
    intro f
    have hr : Relational.schemaArity f.1 ≤ s+1 := by unfold Relational.schemaArity; split <;> omega
    exact (level_sum ((level_unit (by omega)).lift (show 0 ≤ 1 by omega)) (level_fin hr)).lift (by omega)
  exact level_map (level_sum (ha.lift (by omega)) (level_sigma hf hp)) _

theorem cycles_level {d s : ℕ} (ha : a.Level d s) (hs : 100 ≤ s) (hd : 1 ≤ d)
    (ht : ∀ r t, (test r t).cost ≤ budget d s) : (cycles A a test).Level (d+12) s := by
  apply level_sigma (incidence_level A a test ha hs hd ht)
  intro v
  have hm : markers.length (A.tag v) ≤ s+1 := (markers_bound _).trans (by omega)
  exact (level_map (level_fin hm) _).lift (by omega)

theorem arcs_level {d s : ℕ} (ha : a.Level d s) (hs : 100 ≤ s) (hd : 1 ≤ d)
    (ht : ∀ r t, (test r t).cost ≤ budget d s) : (arcs A a test).Level (d+14) s := by
  have hf := facts_level A a test ha hs hd ht
  have hp : ∀ f : A.Fact, (fin (Relational.schemaArity f.1)).Level (d+8) s := by
    intro f
    have hr : Relational.schemaArity f.1 ≤ s+1 := by unfold Relational.schemaArity; split <;> omega
    exact (level_fin hr).lift (by omega)
  have hb : bool.Level (d+9) s := (level_bool (by omega)).lift (by omega)
  have hcodes := level_sum (cycles_level A a test ha hs hd ht)
    ((level_prod hb (level_sigma hf hp)).lift (show d+9+2 ≤ d+12 by omega))
  exact bounded_mapInto hcodes _ _ rfl

end SchemaRun
end TreewidthHom.Executable
