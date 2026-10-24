import Lean
open Lean
namespace Port18COHERENCE_Load
def sameDeclaration (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false
def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data

def load : IO (Std.HashMap Name ConstantInfo) := do
  let mut cs : Std.HashMap Name ConstantInfo := {}
  let mut origin : Std.HashMap Name String := {}
  for line in (← IO.FS.readFile "/tmp/port18coherence-snapshots.tsv").splitOn "\n" do
    if line.isEmpty then continue
    let fs := line.splitOn "\t"
    let data ← readComplete fs[1]!
    for c in data.constants do
      if let some prev := cs[c.name]? then
        if !sameDeclaration prev c then
          let proofOnly := match prev,c with
            | .thmInfo a,.thmInfo b => a.toConstantVal == b.toConstantVal
            | _,_ => false
          IO.println ("SELECT_DIFF " ++ (Json.arr #[toJson c.name.toString,toJson origin[c.name]!,toJson fs[0]!,toJson proofOnly]).compress)
          -- This is selection, NOT a declaration equivalence claim. Kernel checking follows.
      else
        cs := cs.insert c.name c
        origin := origin.insert c.name fs[0]!
  return cs

def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ds := c.getUsedConstantsAsSet.toArray
  if let .inductInfo v := c then ds := ds ++ v.all.toArray ++ v.ctors.toArray
  if let .recInfo v := c then
    ds := ds ++ v.all.toArray
    for r in v.rules do ds := ds ++ r.rhs.getUsedConstants
  return ds

def select (cs : Std.HashMap Name ConstantInfo) (seeds : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := seeds.toList
  let mut selected : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if selected.contains n then continue
    let some c := cs[n]? | throw (IO.userError s!"Missing selected dependency {n}")
    selected := selected.insert n c
    pending := (dependencies c).toList ++ pending
  IO.println s!"SELECTED {selected.size}"
  return selected
end Port18COHERENCE_Load
