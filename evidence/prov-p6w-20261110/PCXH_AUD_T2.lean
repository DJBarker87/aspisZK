-- PCXH_AUD_T2: audit module importing only the single root PRVCmb_L187_ROOT; per-theorem #print axioms for theorems with index mod 4 = 2.
import PRVCmb_L187_ROOT
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
    match env.find? c with
    | some (.axiomInfo _) => unionLoop env stack seen (axs.push c)
    | some ci =>
      let (stack, seen) := (usedOf ci).foldl (fun (p : Array Name × Std.HashSet Name) u => if p.2.contains u then p else (p.1.push u, p.2.insert u)) (stack, seen)
      unionLoop env stack seen axs
    | none => unionLoop env stack seen axs
def unionAxioms (env : Environment) (ns : Array Name) : Array Name := unionLoop env ns (ns.foldl (fun s n => s.insert n) {}) #[]
/-- one audit pass: kind and axioms of every non-internal constant under `root`, then the shared-visited union. -/
def auditRoot (label : String) (pred : Name → Bool) (doUnion : Bool) (k m : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let ns := targets env pred
  let t0 ← IO.monoMsNow
  IO.println s!"PRVCMB_AUDIT_TARGETS {label} {ns.size}"
  let t1a ← IO.monoMsNow
  if doUnion then
    let un := unionAxioms env (ns.map (·.1))
    let t1b ← IO.monoMsNow
    IO.println s!"PRVCMB_UNION_AXIOMS {un.toList} ms={t1b - t1a}"
  let t1 ← IO.monoMsNow
  let mut idx := 0
  let mut cnt := 0
  let mut stopped := 0
  for (n, kind) in ns do
    if doUnion then break
    if kind != "theorem" then
      if k == 0 then IO.println s!"PRVEQ_KIND {n} {kind}"
      continue
    idx := idx + 1
    if idx % m != k then continue
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
#eval PRVCmbAudit.auditRoot "PRV*/PCVE*/PCVB*" (fun n => let r := n.getRoot.toString; let s := n.toString; ["PCVN_","PCVP_","PCVQ_","PCVS_","PCVK_","PCVL_","PCVH_","PCVU_"].any (fun k => (s.splitOn k).length > 1) || r.startsWith "PRV" || r.startsWith "PCVE" || r.startsWith "PCVB" || (n.toString.splitOn ".PRVEq.").length > 1 || (n.toString.splitOn ".PRVFresh_").length > 1) false 2 4
