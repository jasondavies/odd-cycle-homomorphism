module
public import TreewidthHom.MeasuredSchema
@[expose] public section
set_option synthInstance.maxSize 1000
set_option backward.isDefEq.respectTransparency false
namespace TreewidthHom.Executable
open EnumRun
variable {V : Type} [DecidableEq V]
variable (A : Relational (Fin 6) Relational.schemaArity V)
variable [∀ r, DecidablePred (A.holds r)] {vs : Enumeration V}
variable (a : EnumRun vs) (test : ∀ r t, Measured (Decidable (A.holds r t)))

/-- The prepared vertex and arc lists are the measured computations' outputs,
not separately recomputed non-instrumented lists. -/
def relationalMeasured (eqCost : ℕ) : Measured (ℕ × List (ℕ × ℕ)) :=
  let dv := SchemaRun.cycles A a test
  let es := SchemaRun.arcs A a test
  let out := indexedAssemblyMeasured (A.typedDag.encoded markers).assembly dv.output es.output eqCost
  ⟨out.value,dv.run.cost+es.run.cost+out.cost+1⟩

theorem relationalMeasured_value (eqCost : ℕ) :
    (relationalMeasured A a test eqCost).value = (relationalGraph A vs).data := by
  simp only [relationalMeasured,indexedAssemblyMeasured_value,EnumRun.output_eq]
  rfl

theorem absorb_serialization (b : ℕ) :
    2*b+10000*(b+2)*(b+1)^2+1 ≤ grow (grow b) := by
  have hb := le_grow b
  have h1 : 10000*(b+2)*(b+1)^2 ≤ 200*grow b := by
    unfold grow
    nlinarith [Nat.zero_le (b^3)]
  have h2 : 203*grow b ≤ grow (grow b) := by
    generalize grow b = g
    unfold grow
    nlinarith [Nat.zero_le (g^2),Nat.zero_le (g^3)]
  have hg : 1 ≤ grow b := by
    have hp : 0 < (b+1)^3 := pow_pos (by omega) _
    unfold grow
    omega
  omega

theorem relationalMeasured_cost {d s eqCost : ℕ} (ha : a.Level d s)
    (hs : 100 ≤ s) (hd : 1 ≤ d)
    (ht : ∀ r t, (test r t).cost ≤ budget d s) (heq : eqCost ≤ budget d s) :
    (relationalMeasured A a test eqCost).cost ≤ budget (d+16) s := by
  have hv := (SchemaRun.cycles_level A a test ha hs hd ht).lift (show d+12 ≤ d+14 by omega)
  have he := SchemaRun.arcs_level A a test ha hs hd ht
  have hh := indexedAssemblyMeasured_quadratic (A.typedDag.encoded markers).assembly
    (SchemaRun.cycles A a test).output (SchemaRun.arcs A a test).output eqCost
    (budget (d+14) s)
    (by rw [EnumRun.output_eq]; exact hv.1)
    (by rw [EnumRun.output_eq]; exact he.1)
  have hq := heq.trans (budget_mono (show d ≤ d+14 by omega) s)
  have hm := Nat.mul_le_mul_right ((budget (d+14) s+1)^2)
    (Nat.mul_le_mul_left 10000 (Nat.add_le_add_right hq 2))
  have hb := absorb_serialization (budget (d+14) s)
  have h1 := hv.2
  have h2 := he.2
  change _ ≤ grow (grow (budget (d+14) s))
  dsimp only [relationalMeasured]
  omega

end TreewidthHom.Executable
