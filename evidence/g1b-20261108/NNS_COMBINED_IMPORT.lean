import NNM_COMBINED_IMPORT
import NVR_COMBINED_IMPORT
import FIN_COMBINED_IMPORT
import LIBW_WeakPerEnv
import NNP_COMBINED_IMPORT
import NNS_SameConstant
import NNS_Fold241
import NNS_LibraryContext
import NNS_PortLaw241
import NNS_RelReplay241
import NNS_SelectionObligation
import NNS_Field
import NNS_Canonical241
import NNS_064Value

run_cmd do
 let env ← Lean.getEnv
 for n in env.header.moduleNames do
  IO.println s!"NNS_MODULE {n}"
