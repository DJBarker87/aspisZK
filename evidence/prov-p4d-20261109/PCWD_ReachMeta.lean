import Lean
import NNN_COMBINED_IMPORT
open Lean Meta Elab

namespace PCWD

def isS1 (n : Name) : Bool := n.getRoot.toString.startsWith "AspisS1ValuesOwned"
def isS1Core (n : Name) : Bool := n.getRoot == `AspisS1ValuesOwned
def isNFU (n : Name) : Bool := n.toString.endsWith "compact.expand_values"

def typeDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci => ci.type.getUsedConstants

def allDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let t := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | some e => t ++ e.getUsedConstants
    | none => t

structure Graph where
  names : Array Name
  adj : Array (Array Nat)

partial def build (env : Environment) (root : Name) : Graph := Id.run do
  let mut names : Array Name := #[root]
  let mut idx : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert root 0
  let mut adj : Array (Array Nat) := #[]
  let mut i := 0
  while i < names.size do
    let n := names[i]!
    let mut out : Array Nat := #[]
    for d in allDeps env n do
      match idx[d]? with
      | some j => out := out.push j
      | none =>
        let j := names.size
        names := names.push d
        idx := idx.insert d j
        out := out.push j
    adj := adj.push out
    i := i + 1
  return { names := names, adj := adj }

/-- BFS from index 0 avoiding `blocked`; returns parent array (none = unreached; root parent = itself). -/
def bfs (g : Graph) (blocked : Array Bool) : Array (Option Nat) := Id.run do
  let mut par : Array (Option Nat) := Array.replicate g.names.size none
  par := par.set! 0 (some 0)
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let u := q[h]!
    h := h + 1
    for v in g.adj[u]! do
      if par[v]!.isNone && !blocked[v]! then
        par := par.set! v (some u)
        q := q.push v
  return par

partial def pathTo (g : Graph) (par : Array (Option Nat)) (v : Nat) : List Name :=
  let rec go (v : Nat) (acc : List Name) (fuel : Nat) : List Name :=
    match fuel with
    | 0 => acc
    | f+1 =>
      let acc := g.names[v]! :: acc
      match par[v]! with
      | some p => if p == v then acc else go p acc f
      | none => acc
  go v [] 10000

def showL (l : List Name) : String := ", ".intercalate (l.map toString)

def analyse (env : Environment) (root : Name) : IO Unit := do
  IO.println s!"=== ROOT {root}"
  if (env.find? root).isNone then
    IO.println "ROOT_NOT_FOUND"; return
  let g := build env root
  let n := g.names.size
  IO.println s!"reachable_total {n}"
  let noBlock := Array.replicate n false
  let par := bfs g noBlock
  -- reverse adjacency
  let mut rev : Array (Array Nat) := Array.replicate n #[]
  for u in [0:n] do
    for v in g.adj[u]! do
      rev := rev.modify v (·.push u)
  let s1 := (List.range n).filter (fun i => isS1 g.names[i]!)
  let s1core := s1.filter (fun i => isS1Core g.names[i]!)
  IO.println s!"s1_family_reached {s1.length}"
  IO.println s!"s1_core_reached {s1core.length}"
  for i in s1core do IO.println s!"S1CORE {g.names[i]!}"
  for i in s1 do
    if !isS1Core g.names[i]! then IO.println s!"S1FAM {g.names[i]!}"
  -- B: reached theorems whose type mentions an S1-family constant and an NFU expand_values constant
  let mut bset : Array Bool := Array.replicate n false
  let mut bl : List Nat := []
  for i in [0:n] do
    let nm := g.names[i]!
    match env.find? nm with
    | some (.thmInfo _) =>
      let ds := typeDeps env nm
      if ds.any isS1 && ds.any isNFU then
        bset := bset.set! i true; bl := i :: bl
    | _ => pure ()
  IO.println s!"B_theorems_count {bl.length}"
  -- reaches-S1-core set (reverse BFS)
  let mut canReach : Array Bool := Array.replicate n false
  let mut q : Array Nat := #[]
  for i in s1core do
    canReach := canReach.set! i true; q := q.push i
  let mut h := 0
  while h < q.size do
    let u := q[h]!
    h := h + 1
    for p in rev[u]! do
      if !canReach[p]! then
        canReach := canReach.set! p true; q := q.push p
  for i in bl.reverse do
    IO.println s!"B {g.names[i]!} reaches_s1core={canReach[i]!} in_reach_from_root={par[i]!.isSome}"
  -- NFU constants reached
  for i in [0:n] do
    if isNFU g.names[i]! then IO.println s!"NFU_REACHED {g.names[i]!}"
  -- witness path to first (BFS order) S1 core and S1 family constants
  let mut shown := 0
  for i in s1core do
    if shown < 3 && par[i]!.isSome then
      IO.println s!"WITNESS_CORE {g.names[i]!} : {showL (pathTo g par i)}"
      shown := shown + 1
  -- unblocked entries: S1-family constants with non-S1 predecessors in reach
  let mut cnt := 0
  for i in s1 do
    for p in rev[i]! do
      if !isS1 g.names[p]! && par[p]!.isSome && cnt < 400 then
        IO.println s!"S1_ENTRY {g.names[p]!} -> {g.names[i]!} pred_on_path_from_root={par[p]!.isSome}"
        cnt := cnt + 1
  -- consumers of B theorems
  for b in bl.reverse do
    for p in rev[b]! do
      IO.println s!"B_CONSUMER {g.names[p]!} uses {g.names[b]!}"
  -- blocked BFS
  let par2 := bfs g bset
  let s1b := s1core.filter (fun i => par2[i]!.isSome)
  IO.println s!"blocked_s1_core_reached {s1b.length}"
  let mut shown2 := 0
  for i in s1b do
    if shown2 < 3 then
      IO.println s!"WITNESS_BLOCKED {g.names[i]!} : {showL (pathTo g par2 i)}"
      shown2 := shown2 + 1
  let s1fb := s1.filter (fun i => !isS1Core g.names[i]! && par2[i]!.isSome)
  IO.println s!"blocked_s1_family_noncore_reached {s1fb.length}"
  let mut shown3 := 0
  for i in s1fb do
    if shown3 < 3 then
      IO.println s!"WITNESS_BLOCKED_FAM {g.names[i]!} : {showL (pathTo g par2 i)}"
      shown3 := shown3 + 1

end PCWD

open PCWD in
#eval show MetaM Unit from do
  let env ← getEnv
  analyse env `AspisR1.RPx_Deployed.deployed
  analyse env `AspisR1.NHS_CheckpointPacket.source
