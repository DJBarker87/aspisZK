import NGV_COMBINED_IMPORT
import S1NativeCompactModelV1
import NFU_LPn_ExpandTrace
open Aeneas Aeneas.Std Result
#print core.slice.index.SliceIndexRangeUsizeSlice.index
#print core.slice.index.SliceIndexRangeUsizeSlice.index_mut
#print List.setSlice!
#print NFU_Retarget.LPl_Kit_Release.compact.CodecError
#print AspisR1CurrentCaller.compact.CodecError
#print NFQ_RowShape.compact_reference
run_cmd do
 for (n,c) in (←Lean.getEnv).constants.toList do
  if (n.toString.contains "setSlice!" && !n.toString.contains "_proof" && !n.toString.contains "_simp") then
   Lean.logInfo m!"{n}: {c.type}"
