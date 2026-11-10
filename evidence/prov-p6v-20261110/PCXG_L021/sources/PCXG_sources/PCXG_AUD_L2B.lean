-- PCXG audit module PCXG_AUD_L2B (stage2 NOC PCVP): imports the credited modules by reference, then one audit pass over every constant whose name contains one of: "PCVP_"
import Aeneas
import PRVEq_AdapterStage2DeployedNOC_o1
section PRVCmbAuditDef
open Lean Elab Command
namespace PRVCmbAudit
def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM" | .opaqueInfo _ => "opaque" | _ => "other"
def targets (env : Environment) (pred : Name → Bool) : Array (Name × String) :=
  let r := env.constants.fold (fun (acc : Array (Name × String)) n ci =>
    if pred n && !n.isInternal then acc.push (n, kindOf ci) else acc) #[]
  r.qsort (fun a b => Name.lt a.1 b.1)
def usedOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | .axiomInfo _ => #[]
  | _ => t
/-- iterative (stack-safe) shared-visited traversal: the union of axioms of all constants in `ns`. -/
partial def unionLoop (env : Environment) (stack : Array Name) (seen : Std.HashSet Name) (axs : Array Name) : Array Name :=
  match stack.back? with
  | none => axs
  | some c =>
    let stack := stack.pop
    if seen.contains c then unionLoop env stack seen axs
    else
      let seen := seen.insert c
      match env.find? c with
      | some (.axiomInfo _) => unionLoop env stack seen (axs.push c)
      | some ci => unionLoop env (stack ++ usedOf ci) seen axs
      | none => unionLoop env stack seen axs
def unionAxioms (env : Environment) (ns : Array Name) : Array Name := unionLoop env ns {} #[]
/-- one audit pass: kind and axioms of every non-internal constant under `root`, then the shared-visited union. -/
def auditRoot (label : String) (pred : Name → Bool) : CommandElabM Unit := do
  let env ← getEnv
  let ns := targets env pred
  let t0 ← IO.monoMsNow
  IO.println s!"PRVCMB_AUDIT_TARGETS {label} {ns.size}"
  let un := unionAxioms env (ns.map (·.1))
  let t1 ← IO.monoMsNow
  IO.println s!"PRVCMB_UNION_AXIOMS {un.toList} ms={t1 - t0}"
  let mut cnt := 0
  let mut stopped := 0
  for (n, kind) in ns do
    if kind != "theorem" then
      IO.println s!"PRVEQ_KIND {n} {kind}"
      continue
    let now ← IO.monoMsNow
    if now - t0 > 110000 then
      stopped := stopped + 1
      IO.println s!"PRVEQ_KIND {n} {kind}"
      IO.println s!"PRVCMB_PERITEM_SKIPPED_TIME_GUARD {n}"
      continue
    let ax ← collectAxioms n
    cnt := cnt + 1
    IO.println s!"PRVEQ_KIND {n} {kind}"
    if ax.isEmpty then IO.println s!"'{n}' does not depend on any axioms"
    else IO.println s!"'{n}' depends on axioms: {ax.toList}"
  let t2 ← IO.monoMsNow
  IO.println s!"PRVEQ_AUDIT_COUNT {cnt} skipped_by_time_guard={stopped} ms={t2 - t1}"
  let loc := env.constants.fold (fun (acc : Array Name) n ci => match ci with | .axiomInfo _ => if pred n || (n.toString.splitOn "PRVFresh_").length > 1 then acc.push n else acc | _ => acc) #[]
  IO.println s!"PRVEQ_LOCAL_AXIOM_DECLS {loc.size} {loc.toList}"
end PRVCmbAudit
end PRVCmbAuditDef
#eval PRVCmbAudit.auditRoot "stage2 NOC PCVP" (fun n => let s := n.toString; ["PCVP_"].any (fun k => (s.splitOn k).length > 1))
