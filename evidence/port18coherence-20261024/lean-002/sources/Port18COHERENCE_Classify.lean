import Lean
open Lean
-- Diagnostic normalization only: never used to construct a proof or bypass checking.
private partial def norm : Expr → Expr
  | .mdata _ e => norm e
  | .lam _ t b i => .lam .anonymous (norm t) (norm b) i
  | .forallE _ t b i => .forallE .anonymous (norm t) (norm b) i
  | .letE _ t v b n => .letE .anonymous (norm t) (norm v) (norm b) n
  | .app f a => .app (norm f) (norm a)
  | .proj s n e => .proj s n (norm e)
  | e => e
private def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty")
  pure data
private def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
#eval show IO Unit from do
  for line in (← IO.FS.readFile "input.tsv").splitOn "\n" do
    if line.isEmpty then continue
    let f := line.splitOn "\t"
    let a ← readComplete f[1]!
    let b ← readComplete f[2]!
    let mut bm : Std.HashMap Name ConstantInfo := {}
    for c in b.constants do bm := bm.insert c.name c
    let mut rows : Array Json := #[]
    for c in a.constants do
      match bm[c.name]? with
      | none => rows := rows.push (Json.arr #[toJson c.name.toString, toJson (kind c), toJson "missing"])
      | some d =>
        let ty := c.type == d.type
        let nty := norm c.type == norm d.type
        let value := c.value? == d.value?
        let nvalue := c.value?.map norm == d.value?.map norm
        if !ty || (!value && kind c != "theorem") then
          rows := rows.push (Json.arr #[toJson c.name.toString,toJson (kind c),
            toJson ty,toJson nty,toJson value,toJson nvalue])
        -- Exact before/after terms for smallest program/structure frontier.
        if ["Aeneas.Std.core.fmt.Formatter", "LiteralByteProtocol.Decoder",
            "AdapterRw.r1_pool_adapter.owned.stage1_owned", "AdapterRw.r1_pool_adapter.owned.stage2_owned"].contains c.name.toString then
          IO.println ("TERMS " ++ (Json.arr #[toJson c.name.toString,
            toJson (reprStr (c.type,c.value?)),toJson (reprStr (d.type,d.value?))]).compress)
    IO.println ("CLASS " ++ (Json.arr #[toJson f[0]!,toJson a.constants.size,toJson b.constants.size,Json.arr rows]).compress)
