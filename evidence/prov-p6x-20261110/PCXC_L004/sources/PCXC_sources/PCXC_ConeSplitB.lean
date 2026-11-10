import Lean
open Lean

/-! PCXC cone walker, memory-light variant (the import-based PCXC_WalkTemplate shape was killed at -M7000 on the TAS_FinalB import, PCXC_L003).
    It does NOT import the gate: it reads the .olean files of the import closure with `readModuleData` (memory-mapped, no environment
    construction), keeps adjacency only for constants whose name is in the given pinned cone list(s), and runs BFS with parent pointers.
    Edge relation: constants used by the type and by the value (opaque values included), the same as PCWD_ReachMeta2. -/
namespace PCXC

def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then Name.mkNum n c.toNat! else Name.mkStr n c) Name.anonymous

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax" | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "op" | .quotInfo _ => "quot"

def depsOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some e => t ++ e.getUsedConstants
  | none => t

def loadClosure (roots : List Name) : IO (Array ModuleData) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  let mut out : Array ModuleData := #[]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | m :: rest =>
      stack := rest
      if !seen.contains m then
        seen := seen.insert m
        let fn ← findOLean m
        let (data, _) ← readModuleData fn
        out := out.push data
        if data.isModule then
          -- module-system file: theorem bodies and private declarations live in the server/private parts (as in `importModules` at level private)
          let parts ← readModuleDataParts #[fn, OLeanLevel.server.adjustFileName fn, OLeanLevel.private.adjustFileName fn]
          out := out.push (parts.back?.map (·.1)).get!
        for i in data.imports do
          stack := i.module :: stack
  return out

def pathTo (par : Std.HashMap Name Name) (v : Name) : List Name := Id.run do
  let mut acc : List Name := []
  let mut cur := v
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    acc := cur :: acc
    match par[cur]? with
    | some p => if p == cur then return acc else cur := p
    | none => return acc
  return acc

def run (listFiles : List String) (rootMods : List Name) (roots : List Name) (targets : List Name) : IO Unit := do
  let mut hs : Std.HashMap UInt64 String := {}
  let mut nlist := 0
  for f in listFiles do
    for l in (← IO.FS.readFile f).splitOn "\n" do
      let s := l.trim
      if !s.isEmpty then
        hs := hs.insert (parseName s).hash s
        nlist := nlist + 1
  IO.println s!"PCXC_LIST_NAMES {nlist} distinct_hashes {hs.size}"
  let mods ← loadClosure rootMods
  IO.println s!"PCXC_MODULES_LOADED {mods.size}"
  let mut adj : Std.HashMap Name (Array Name) := {}
  let mut kinds : Std.HashMap Name String := {}
  let mut nconst := 0
  for d in mods do
    for ci in d.constants do
      nconst := nconst + 1
      if hs.contains ci.name.hash then
        -- a later part (private) carries the full theorem/definition; never let a weakened axiom entry overwrite a fuller one
        let k := kindOf ci
        if !(adj.contains ci.name) || k != "ax" then
          adj := adj.insert ci.name (depsOf ci)
          kinds := kinds.insert ci.name k
  IO.println s!"PCXC_CONSTANTS_SCANNED {nconst} MATCHED_LIST_NAMES {adj.size}"
  let mut shown := 0
  for (h, s) in hs.toList do
    if shown < 5 && !(adj.contains (parseName s)) then
      IO.println s!"PCXC_LIST_NAME_NOT_FOUND {s}"
      shown := shown + 1
  for root in roots do
    IO.println s!"PCXC_ROOT {root}"
    if !(adj.contains root) then
      IO.println "PCXC_ROOT_NOT_FOUND"
    else
      let mut par : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
      let mut q : Array Name := #[root]
      let mut h := 0
      let mut missing := 0
      while h < q.size do
        let u := q[h]!
        h := h + 1
        match adj[u]? with
        | none => missing := missing + 1
        | some ds =>
          for v in ds do
            if !par.contains v then
              par := par.insert v u
              q := q.push v
      IO.println s!"PCXC_REACHABLE_TOTAL {root} {q.size} nodes_without_adjacency {missing}"
      for t in targets do
        match par[t]? with
        | none => IO.println s!"PCXC_TARGET {t} NOT_REACHED_FROM {root}"
        | some _ =>
          let p := pathTo par t
          let ks := p.map (fun x => (kinds[x]?).getD "?")
          let nthm := (ks.filter (· == "thm")).length
          IO.println s!"PCXC_TARGET {t} REACHED_FROM {root} hops={p.length - 1} theorem_nodes_on_path={nthm}"
          IO.println s!"PCXC_PATH {t} :: {root} :: {", ".intercalate (p.map fun x => s!"{x}[{(kinds[x]?).getD "?"}]")}"

end PCXC

#eval show IO Unit from do
  PCXC.run ["PCXC_data/splitB.txt"] [`TAS_FinalB] [`AspisR1.TAS_FinalB.deployed_splitB] [`AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value, `AspisR72Sampler.field.r23_product_u32_bounded, `AspisR72Sampler.field.r24_canonical_mul, `AspisR72Sampler.field.r24_canonical_mul.PP, `AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call, `AspisR72Sampler.field.r24_canonical_mul.closure, `AspisR1ClaimsUnrolledParent.candidate_claims.claims, `NJT_ClaimsRef.r1_semantic.NJT_claims_ref]
