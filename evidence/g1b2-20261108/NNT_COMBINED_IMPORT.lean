import NNN_COMBINED_IMPORT
import NNS_COMBINED_IMPORT
import NNT_Interfaces
import NNT_Verify241
import NNT_Port241
import NNT_RelReplay241
import NNT_Native241
import NNT_Root241
import NNT_Field
import NNT_LawOk
import NNT_G1aLaw
import NNT_WeakEntryLaw
import NNT_TopL

run_cmd do
 let env ← Lean.getEnv
 for n in env.header.moduleNames do
  IO.println s!"NNT_MODULE {n}"
