import Aeneas
import Lean
import PRVH_WrapAdd
section PRVCmbAuditDef
open Lean Elab Command
namespace PRVCmbAudit
def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM" | .opaqueInfo _ => "opaque" | _ => "other"
def targets (env : Environment) (root : Name) : Array (Name × String) :=
  let r := env.constants.fold (fun (acc : Array (Name × String)) n ci =>
    if root.isPrefixOf n && !n.isInternal then acc.push (n, kindOf ci) else acc) #[]
  r.qsort (fun a b => Name.lt a.1 b.1)
def unionAxioms (env : Environment) (ns : Array Name) : Array Name :=
  let act : CollectAxioms.M Unit := ns.forM CollectAxioms.collect
  (((act.run env).run {}).2).axioms
/-- one audit pass: kind and axioms of every non-internal constant under `root`, then the shared-visited union. -/
def auditRoot (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let ns := targets env root
  let t0 ← IO.monoMsNow
  IO.println s!"PRVCMB_AUDIT_TARGETS {root} {ns.size}"
  let un := unionAxioms env (ns.map (·.1))
  let t1 ← IO.monoMsNow
  IO.println s!"PRVCMB_UNION_AXIOMS {un.toList} ms={t1 - t0}"
  let mut cnt := 0
  for (n, kind) in ns do
    let ax ← collectAxioms n
    cnt := cnt + 1
    IO.println s!"PRVEQ_KIND {n} {kind}"
    if ax.isEmpty then IO.println s!"'{n}' does not depend on any axioms"
    else IO.println s!"'{n}' depends on axioms: {ax.toList}"
  let t2 ← IO.monoMsNow
  IO.println s!"PRVEQ_AUDIT_COUNT {cnt} ms={t2 - t1}"
  let loc := env.constants.fold (fun (acc : Array Name) n ci => match ci with | .axiomInfo _ => if root.isPrefixOf n then acc.push n else acc | _ => acc) #[]
  IO.println s!"PRVEQ_LOCAL_AXIOM_DECLS {loc.size} {loc.toList}"
end PRVCmbAudit
end PRVCmbAuditDef

#eval PRVCmbAudit.auditRoot `PRVH
