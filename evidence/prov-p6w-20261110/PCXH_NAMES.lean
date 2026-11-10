-- PCXH_NAMES: declaration-name clash scan over the credited modules' olean files (read-only, by reference to the PCXG exports); no import of the modules, so the clashes cannot stop it.
import Lean
open Lean
def mods : List String := ["PRVH_WrapAdd", "PRVCmb_C01", "PRVCmb_C02", "PRVCmb_C03", "PRVCmb_C04", "PRVCmb_C05", "PRVCmb_C06", "PRVCmb_C07", "PRVCmb_C08", "PRVCmb_C09", "PRVCmb_C10", "PRVCmb_C11", "PRVCmb_C12", "PRVCmb_C13", "PRVCmb_C14", "PRVCmb_C15", "PRVCmb_C16", "PRVCmb_C17", "PRVCmb_C19", "PRVCmb_C20", "PRVCmb_C21", "PRVCmb_C22", "PRVCmb_C18A", "PRVCmb_C18B", "PRVCmb_C18C", "PRVCmb_C18D", "PRVEq_VTop_l1", "PRVEq_Tx2Deployed_n0", "PRVEq_PCVH_R1CandidateWideParserSource_k1", "PRVEq_Op2_p5", "PRVEq_Op13_p1", "PRVEq_Op17_p2", "PRVEq_Tx2Deployed_n1", "PRVEq_Resume_q13", "PRVEq_Tx2Deployed_q5", "PRVEq_Validate_q2", "PRVEq_Tx2Deployed_q6", "PRVEq_DeriveRef_q1", "PRVEq_E32_s4", "PRVEq_Tx2Deployed_s1", "PRVEq_WideBind_s2", "PRVEq_Op17_s2", "PRVEq_CkptSmall_s4", "PRVEq_Tx2Deployed_s2", "PRVEq_AdapterStage1_o1", "PRVEq_AdapterStage1DeployedNOC_o1", "PRVEq_NocStage1Compose_o1", "PRVEq_AdapterStage2_o1", "PRVEq_AdapterStage2DeployedNOC_o1", "PRVEq_CallerPrepTx1_o1", "PRVEq_CallerPrepTx1DeployedNOC_o1", "PRVEq_NocPrepTx1Compose_o1", "PRVEq_NocCallerSlots_o1", "PRVEq_NocCallerSlots2_o1"]
def main : IO Unit := do
  let mut seen : Std.HashMap Name (List String) := {}
  let mut total := 0
  for m in mods do
    let (md, _) ← readModuleData (System.FilePath.mk ("/home/dombarker/project-offloads/codex-pc-prov-p6v-20261110/PCXG_exports/" ++ m ++ ".olean"))
    for n in md.constNames do
      if !n.isInternal then
        total := total + 1
        seen := seen.insert n (m :: (seen.getD n []))
  IO.println s!"PCXH_NAMES_TOTAL {total} DISTINCT {seen.size}"
  let mut cl := 0
  for (n, ms) in seen.toList do
    if ms.length > 1 then
      cl := cl + 1
      IO.println s!"PCXH_CLASH {n} {ms}"
  IO.println s!"PCXH_CLASH_COUNT {cl}"
#eval main
