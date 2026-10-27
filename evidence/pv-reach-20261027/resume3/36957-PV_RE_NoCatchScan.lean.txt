import R1Z.PV_RE_NoCatchGenerator
open Lean Meta Elab Command Term
namespace R1Z.PV_RE_NoCatchScan

def dictionaryParam (n : Name) : MetaM Bool := do
  let c ← getConstInfo n
  match c.type with
  | .forallE _ (.const `ProverRwFull.ExternalTypes _) b _ =>
    match b with
    | .forallE _ t _ _ => return t.getAppFn.constName? == some `ProverRwFull.ExternalFuns
    | _ => return false
  | _ => return false

/-- Inspect symbolic source constants only; do not evaluate an application. -/
partial def closure (n : Name) (seen : Array Name) : TermElabM (Array Name × Array Name) := do
  if seen.contains n then return (seen, #[])
  let mut seen := seen.push n
  if n.getPrefix == `ProverRwFull.ExternalFuns then return (seen, #[n])
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "opaque project consumer {n}"
  let mut ops := #[]
  let mut consumers := #[]
  for dep in value.getUsedConstants do
    if dep.toString.startsWith "Aeneas.Std.Result." then
      consumers := consumers.push dep
    if dep != n && (← dictionaryParam dep) && !(← isProp (← getConstInfo dep).type) then
      let (more, os) ← closure dep seen
      seen := more
      for op in os do
        if !ops.contains op then ops := ops.push op
  logInfo m!"NO_CATCH_SCAN {n}: Result-constants {consumers.toList}"
  return (seen, ops)

elab "pv_scan_no_catch " n:ident : command => do
  liftTermElabM do
    let (seen, ops) ← closure n.getId #[]
    let sorted := ops.qsort (fun a b => a.toString < b.toString)
    logInfo m!"STATIC_SUPPORT {n.getId}: {sorted.toList}"
    logInfo m!"SOURCE_CLOSURE_SIZE {seen.size}"
end R1Z.PV_RE_NoCatchScan
