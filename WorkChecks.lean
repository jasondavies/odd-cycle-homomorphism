import TreewidthHom.IndexedAssemblyCost
import TreewidthHom.MeasuredDecision
open TreewidthHom TreewidthHom.Executable

def testAssembly : Arrow.Assembly (Fin 2) Unit :=
  ⟨fun _ => 0,fun _ => 1,by decide⟩

def main : IO Unit := do
  let vs := Enumeration.fin 2
  let es := Enumeration.unit
  let out := indexedAssembly testAssembly vs es
  for c in [0,1,5,17] do
    let run := indexedAssemblyMeasured testAssembly vs es c
    unless run.value == out.data do throw (IO.userError "measured serializer changed the output")
    unless run.cost ≤ 10000*(c+2)*(out.order+1)^2 do
      throw (IO.userError "measured serializer exceeded its proved bound")
  for n in List.range 12 do
    let r := Measured.finRange n
    unless r.value == List.finRange n && r.cost ≤ (n+1)^2 do
      throw (IO.userError "measured range regression")
  IO.println "PASS: 4 measured-serialization executions and 12 measured finite ranges."
