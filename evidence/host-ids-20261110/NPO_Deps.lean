import TAS_FinalB
/-! NPO_: dependency map. For every constant reachable from the run-7 roots, the set of
id targets it depends on transitively (type or value), its own direct target uses, and
whether its TYPE (statement) depends. Read-only; adds no declaration. -/
open Lean
namespace NPO_Deps
def targets : Array Name := #[
  `AspisR1.CPH_Program.verifier,       -- bit 0
  `NHJ_IdPacket.poolDefault,           -- bit 1
  `NHJ_IdPacket.registryDefault,       -- bit 2
  `NHJ_IdPacket.poolDevnet,            -- bit 3
  `NHJ_IdPacket.registryDevnet,        -- bit 4
  `NHJ_IdReference.ids_ref,            -- bit 5
  `LIB_Deployed.deployed,              -- bit 6
  `LIB_Instances.D,                    -- bit 7
  `LIB_Deployed.ids,                   -- bit 8
  `NHJ_IdPacket.pool,                  -- bit 9
  `NHJ_IdPacket.registry]              -- bit 10
def roots : Array Name := #[`AspisR1.TAS_FinalB.deployed_splitB, `AspisR1.TAS_FinalB.deployed_charge,
  `AspisR1.TAS_FinalB.fail_sub_rec, `AspisR1.NNH8_DeployedOuter]
def baseBits (n : Name) : UInt32 := Id.run do
  let mut b : UInt32 := 0
  for i in [0:targets.size] do
    if targets[i]! == n then b := b ||| ((1 : UInt32) <<< i.toUInt32)
  return b
def deps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => t ++ v.getUsedConstants
  | none => match ci with
    | .inductInfo ii => t ++ ii.ctors.toArray
    | _ => t
def kind : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .inductInfo _ => "induct" | .quotInfo _ => "quot"
def run : CoreM Unit := do
  let env ← getEnv
  let mut memo : Std.HashMap Name UInt32 := {}
  let mut stack : Array (Name × Bool) := roots.map (·, false)
  while h : stack.size > 0 do
    let (n, ex) := stack.back
    stack := stack.pop
    if memo.contains n then continue
    match env.find? n with
    | none => memo := memo.insert n 0
    | some ci =>
      let ds := deps ci
      if !ex then
        stack := stack.push (n, true)
        for d in ds do
          if !memo.contains d then stack := stack.push (d, false)
      else
        let mut b := baseBits n
        for d in ds do b := b ||| memo.getD d 0
        memo := memo.insert n b
  let mut out : Array String := #[]
  let mut nDep := 0
  for (n, b) in memo.toList do
    if b == 0 then continue
    nDep := nDep + 1
    let some ci := env.find? n | continue
    let mut tb : UInt32 := baseBits n
    for d in ci.type.getUsedConstants do tb := tb ||| memo.getD d 0
    let mut direct : UInt32 := 0
    for d in deps ci do direct := direct ||| baseBits d
    let modName := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!).toString | none => "?"
    let j := Json.mkObj [("n", toJson n.toString), ("k", toJson (kind ci)), ("m", toJson modName),
      ("bits", toJson b.toNat), ("type_bits", toJson tb.toNat), ("direct", toJson direct.toNat)]
    out := out.push j.compress
  IO.FS.writeFile "NPO_DEPS.jsonl" (String.intercalate "\n" out.toList ++ "\n")
  IO.println s!"NPO_DEPS reachable={memo.size} dependents={nDep}"
#eval run
end NPO_Deps
