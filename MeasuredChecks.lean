import TreewidthHom.MeasuredReduction
open TreewidthHom TreewidthHom.Executable

/-- Execution regressions supplement the general kernel-checked equalities.
Do not evaluate the deliberately loose iterated-polynomial bound numerically. -/
def main : IO Unit := do
  let cases : List (String × List (List Bool) × Nat × Nat) := [
    ("empty input", [], 2^256, 7),
    ("zero length", [[false,true]], 0, 3),
    ("empty word", [[]], 1, 1),
    ("huge rejection", [[false]], 2^256, 257),
    ("one-word construction", [[false]], 1, 3),
    ("conflicting-word construction", [[false],[true]], 1, 1)]
  for (label,xs,ell,q) in cases do
    let r := compileMeasured xs ell q
    let expected := (compile xs ell).data
    unless r.value == expected do
      throw (IO.userError s!"measured constructor changed output: {label}")
    unless 0 < r.cost do
      throw (IO.userError s!"missing modeled cost: {label}")
    IO.println s!"PASS: {label}; orders {r.value.1.1}, {r.value.2.1}; modeled cost {r.cost}."
