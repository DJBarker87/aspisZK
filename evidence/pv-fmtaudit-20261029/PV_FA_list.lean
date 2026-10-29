import Aeneas
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !(toString mod).startsWith "Aeneas" then continue
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "def"
      | .opaqueInfo _ => "opaque"
      | .thmInfo _ => "theorem"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quot"
    let axs ← collectAxioms n
    let deps := (ci.type.getUsedConstants ++ (ci.value?.getD (.sort .zero)).getUsedConstants).toList.map toString
    let j := Json.mkObj [("name", toJson (toString n)), ("module", toJson (toString mod)), ("kind",toJson kind), ("type_hash",toJson (toString ci.type.hash)), ("value_hash",toJson (ci.value?.map fun v => toString v.hash)), ("axioms",toJson (axs.toList.map toString)), ("dependencies",toJson deps)]
    rows := rows.push j.compress
  for r in rows.qsort (· < ·) do
    logInfo m!"PV_FA_JSON {r}"
