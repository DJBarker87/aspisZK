-- PCXG_ROOT PRVCmb_L187_ROOT: the root module of the L187-closure combined import (bundles C01..C22, PRVH_WrapAdd and the deployed top-body modules). Imports every bundle (and the generic helper PRVH_WrapAdd), then one audit pass over every constant under PRV*/PCVE*/PCVB*.
import Aeneas
import Lean
import PRVH_WrapAdd
import PRVCmb_C01
import PRVCmb_C02
import PRVCmb_C03
import PRVCmb_C04
import PRVCmb_C05
import PRVCmb_C06
import PRVCmb_C07
import PRVCmb_C08
import PRVCmb_C09
import PRVCmb_C10
import PRVCmb_C11
import PRVCmb_C12
import PRVCmb_C13
import PRVCmb_C14
import PRVCmb_C15
import PRVCmb_C16
import PRVCmb_C17
import PRVCmb_C18A
import PRVCmb_C18B
import PRVCmb_C18C
import PRVCmb_C18D
import PRVCmb_C19
import PRVCmb_C20
import PRVCmb_C21
import PRVCmb_C22
import PRVEq_VTop_l1
import PRVEq_Tx2Deployed_n0
import PRVEq_PCVH_R1CandidateWideParserSource_k1
import PRVEq_Op2_p5
import PRVEq_Op13_p1
import PRVEq_Op17_p2
import PRVEq_Tx2Deployed_n1
import PRVEq_Resume_q13
import PRVEq_Tx2Deployed_q5
import PRVEq_Validate_q2
import PRVEq_Tx2Deployed_q6
import PRVEq_DeriveRef_q1
import PRVEq_E32_s4
import PRVEq_Tx2Deployed_s1
import PRVEq_WideBind_s2
import PRVEq_Op17_s2
import PRVEq_CkptSmall_s4
import PRVEq_Tx2Deployed_s2
import PRVEq_AdapterStage1_o1
import PRVEq_AdapterStage1DeployedNOC_o1
import PRVEq_NocStage1Compose_o1
import PRVEq_AdapterStage2_o1
import PRVEq_AdapterStage2DeployedNOC_o1
import PRVEq_CallerPrepTx1_o1
import PRVEq_CallerPrepTx1DeployedNOC_o1
import PRVEq_NocPrepTx1Compose_o1
import PRVEq_NocCallerSlots_o1
import PRVEq_NocCallerSlots2_o1
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

#eval PRVCmbAudit.auditRoot "PRV*/PCVE*/PCVB*" (fun n => let r := n.getRoot.toString; let s := n.toString; ["PCVN_","PCVP_","PCVQ_","PCVS_","PCVK_","PCVL_","PCVH_"].any (fun k => (s.splitOn k).length > 1) || r.startsWith "PRV" || r.startsWith "PCVE" || r.startsWith "PCVB" || (n.toString.splitOn ".PRVEq.").length > 1 || (n.toString.splitOn ".PRVFresh_").length > 1)
