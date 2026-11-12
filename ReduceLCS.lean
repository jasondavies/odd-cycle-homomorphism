import TreewidthHom.ExecutableReduction

open TreewidthHom.Executable

def parseWord (s : String) : Except String (List Bool) :=
  s.toList.mapM (fun c => if c = '0' then .ok false else if c = '1' then .ok true
    else .error "Words must contain only 0 and 1; use an empty argument for an empty word.")

def graphJson (g : EdgeList) : Lean.Json :=
  Lean.Json.mkObj [("vertices",Lean.toJson g.order),("edges",Lean.toJson g.data.2)]

def main (args : List String) : IO UInt32 := do
  let (json,args) := if args.head? = some "--json" then (true,args.drop 1) else (false,args)
  match args with
  | [] =>
    IO.eprintln "Usage: lake env lean --run ReduceLCS.lean [--json] LENGTH [BINARY_WORD ...]"
    return 2
  | n::words =>
    match n.toNat?, words.mapM parseWord with
    | some ell, .ok xs =>
      let p := compile xs ell
      let out := if json then Lean.Json.mkObj [("source",graphJson p.source),("target",graphJson p.target)]
        else Lean.Json.mkObj [
          ("source_vertices",Lean.toJson p.source.order),
          ("source_oriented_edges",Lean.toJson p.source.edges.length),
          ("target_vertices",Lean.toJson p.target.order),
          ("target_oriented_edges",Lean.toJson p.target.edges.length)]
      IO.println out.compress
      return 0
    | none,_ =>
      IO.eprintln "LENGTH must be a nonnegative decimal integer."
      return 2
    | _,.error msg =>
      IO.eprintln msg
      return 2
