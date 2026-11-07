import PCI_DepositActual.Funs
import NFY_Part005
open Lean Elab Command
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if s == "Aeneas.Std.core.array.equality.PartialEqArray.ne" ||
     s == "Aeneas.Std.core.array.equality.PartialEqArray.eq" ||
     s == "Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index" ||
     s == "Aeneas.Std.core.array.TryFromSharedArraySlice.try_from" ||
     s == "Aeneas.Std.core.array.TryFromArrayCopySlice.try_from" ||
     s == "NFY_NBP_DigestDecode.decoded" ||
     s == "Aeneas.Std.core.num.U16.from_le_bytes" ||
     ((s.splitOn "PartialEqArray").length>1 && (s.endsWith "spec" || s.endsWith "spec_simp")) then
   logInfo m!"DEF {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
