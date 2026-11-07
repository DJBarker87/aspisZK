import LIB_VCarriers
import NGM_LPi_TowerValues
import NGO_CallCases
import NGX_Payload
import NGX_StateImpl
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let names := ["CanonicalQM","CanonicalCM","canonQ","Canon","canonical","c1Cell","maskCell","pointAtNat","decodeMain","decode_k","decodeRows","sourceRecord","QM31.add","QM31.mul"]
 for (n,c) in env.constants.toList do
  if names.any (fun s => n.toString.endsWith ("."++s)) then
   if !n.toString.endsWith ".proof_1" then
    logInfo m!"{n} : {c.type}"
#print AspisR1.ExtractedMaskTowerAdd.CanonicalQM
#print AspisR1.ExtractedMaskTowerAdd.CanonicalCM
#print AspisR1.LPi_FieldValues.canonQ
