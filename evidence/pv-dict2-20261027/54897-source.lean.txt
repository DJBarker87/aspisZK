import R1Z.PDict_PureDictionary
import R1Z.PDict_RemainingDictionary231
import R1Z.PDict_FinalTypes
import R1Z.PDict_RowBounds244
import R1Z.PDict_RowChunk244_0
import R1Z.PDict_RowChunk244_1
import R1Z.PDict_RowChunk244_2
import R1Z.PDict_RowChunk244_3
import R1Z.PDict_RowChunk244_4
import R1Z.PDict_RowChunk244_5
import R1Z.PDict_RowChunk244_6
import R1Z.PDict_RowChunk244_7
import R1Z.PDict_RowTable244
import R1Z.PDict_OwnedSource244
import R1Z.PDict_CopySource244
import R1Z.PDict_Advance244
import R1Z.PDict_OwnedCell262
import R1Z.PDict_RowBits262
import R1Z.PDict_RowTotal262
import R1Z.PDict_OwnedPrefix262
import R1Z.PDict_OwnedLoop262
import R1Z.PDict_Tabulate262
import R1Z.PDict_OwnedTarget262
import R1Z.PDict_CoordinatesEq262
import R1Z.PDict_ArrayRead262
import R1Z.PDict_OwnedCorrect262
import R1Z.PV_CB_Op229Transport
import R1Z.PV_Join_DictInspect
import R1Z.PV_Join_Op20Value
import R1Z.PV_CB_PathBorrow
import R1Z.PV_CB_ArrayCarrierObstruction
import R1Z.PDict_RemainingExt231
import R1Z.PDict_RemainingCommute231_01
import R1Z.PDict_RemainingCommute231_02
import R1Z.PDict_RemainingCommute231_03
import R1Z.PDict_RemainingCommute231_04
import R1Z.PDict_RemainingCommute231_05
import R1Z.PDict_RemainingCommute231_06
import R1Z.PDict_RemainingCommute231_07
import R1Z.PDict_RemainingCommute231_08
import R1Z.PDict_RemainingCommute231_09
import R1Z.PDict_RemainingCommute231_10
import R1Z.PDict_RemainingCommute231_11
import R1Z.PDict_RemainingCommute231_12
import R1Z.PDict_RemainingCommute231_13
import R1Z.PDict_RemainingCommute231_14
import R1Z.PDict_RemainingCommute231_15
import R1Z.PDict_RemainingCommute231_16
import R1Z.PDict_RemainingCommute231_17
import R1Z.PDict_RemainingCommute231_18
import R1Z.PDict_RemainingCommute231_19
import R1Z.PDict_RemainingCommute231_20
import R1Z.PDict_RemainingCommute231_21
import R1Z.PDict_RemainingCommute231_22
import R1Z.PDict_RemainingCommute231_23
import Lean
open Lean Elab Command
#print axioms ProverRwFull.ExternalFuns
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    logInfo m!"MODULE|{moduleName}"
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx]!
      let text := owner.toString
      if text.startsWith "R1Z.PDict_" || text == "R1Z.PV_CB_Op229Transport" ||
          text == "R1Z.PV_CB_PathBorrow" || text == "R1Z.PV_CB_ArrayCarrierObstruction" ||
          text == "R1Z.PV_Join_DictInspect" || text == "R1Z.PV_Join_Op20Value" then
        logInfo m!"OWNER|{owner}|{n}"
        elabCommand (← `(command| #print axioms $(mkIdent n)))
