import Lean
open Lean
structure Dag where
  seen : Std.HashMap USize Nat := {}
  interned : Std.HashMap String Nat := {}
  nodes : Array String := #[]
  deriving Inhabited

-- Exact shallow node keys, canonicalized bottom-up. Pointer memoization only
-- avoids repeated visits; equality uses the full constructor/field key string.
unsafe partial def encodeNode (e : Expr) : StateM Dag Nat := do
  if let some i := (← get).seen[ptrAddrUnsafe e]? then return i
  let key ← match e with
    | .bvar i => pure <| Json.arr #[toJson "bvar",toJson i]
    | .fvar i => pure <| Json.arr #[toJson "fvar",toJson (reprStr i)]
    | .mvar i => pure <| Json.arr #[toJson "mvar",toJson (reprStr i)]
    | .sort u => pure <| Json.arr #[toJson "sort",toJson (reprStr u)]
    | .const n us => pure <| Json.arr #[toJson "const",toJson (reprStr n),toJson (reprStr us)]
    | .app f a => do
      let f ← encodeNode f; let a ← encodeNode a
      pure <| Json.arr #[toJson "app",toJson f,toJson a]
    | .lam n t b bi => do
      let t ← encodeNode t; let b ← encodeNode b
      pure <| Json.arr #[toJson "lam",toJson (reprStr n),toJson t,toJson b,toJson (reprStr bi)]
    | .forallE n t b bi => do
      let t ← encodeNode t; let b ← encodeNode b
      pure <| Json.arr #[toJson "forallE",toJson (reprStr n),toJson t,toJson b,toJson (reprStr bi)]
    | .letE n t v b nd => do
      let t ← encodeNode t; let v ← encodeNode v; let b ← encodeNode b
      pure <| Json.arr #[toJson "letE",toJson (reprStr n),toJson t,toJson v,toJson b,toJson nd]
    | .lit v => pure <| Json.arr #[toJson "lit",toJson (reprStr v)]
    | .mdata m e => do
      let e ← encodeNode e
      pure <| Json.arr #[toJson "mdata",toJson (reprStr m),toJson e]
    | .proj n i e => do
      let e ← encodeNode e
      pure <| Json.arr #[toJson "proj",toJson (reprStr n),toJson i,toJson e]
  let key := key.compress
  let s ← get
  let (i,s) := match s.interned[key]? with
    | some i => (i,s)
    | none => (s.nodes.size,{s with interned := s.interned.insert key s.nodes.size, nodes := s.nodes.push key})
  set {s with seen := s.seen.insert (ptrAddrUnsafe e) i}
  return i

unsafe def encodeExpr (e : Expr) : String :=
  let (root,s) := (encodeNode e).run {}
  (Json.mkObj [("root",toJson root),("nodes",toJson s.nodes)]).compress

@[noinline] unsafe def inspect (wanted : Std.HashSet String) (line : String) : IO (Array CompactedRegion) := do
  let stdout ← IO.getStdout
  let fields := line.splitOn "\t"
  let mod := fields[0]!
  let path := fields[1]!
  let (base,region) ← readModuleData path
  let mut parts := #[(base,region)]
  if base.isModule then
    let server ← CompactedRegion.read (α := ModuleData) (path ++ ".server") #[region]
    let priv ← CompactedRegion.read (α := ModuleData) (path ++ ".private") #[region,server.2]
    parts := parts.push server |>.push priv
  for p in parts do
    for c in p.1.constants do
      if wanted.contains c.name.toString then
        let j := Json.mkObj [("module",toJson mod),("name",toJson c.name.toString),
          ("type",toJson (encodeExpr c.type)),("value",toJson ((c.value? true).map encodeExpr)),
          ("level_params",toJson (c.levelParams.map Name.toString))]
        stdout.putStrLn j.compress
        stdout.flush
  return parts.map (·.2)

unsafe def main (args : List String) : IO Unit := do
  -- Positive controls: equal syntax with different allocation/sharing histories.
  let x := Expr.const `x []
  let shared := Expr.app x x
  let separatelyBuilt := Expr.app (Expr.const `x []) (Expr.const `x [])
  unless encodeExpr shared == encodeExpr separatelyBuilt do throw <| IO.userError "DAG positive control failed"
  unless encodeExpr x != encodeExpr (.const `y []) do throw <| IO.userError "DAG negative name control failed"
  unless encodeExpr (.lam `x (.sort .zero) (.bvar 0) .default) != encodeExpr (.lam `y (.sort .zero) (.bvar 0) .default) do
    throw <| IO.userError "DAG binder-name control failed"
  let wanted := (← IO.FS.lines args[1]!).foldl (fun s n => s.insert n) ({} : Std.HashSet String)
  for line in (← IO.FS.lines args[0]!) do
    let regions ← inspect wanted line
    for r in regions.reverse do CompactedRegion.free r
