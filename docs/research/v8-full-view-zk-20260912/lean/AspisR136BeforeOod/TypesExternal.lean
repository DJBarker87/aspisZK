import Aeneas.Std
import AspisR137Transcript.Types

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR136BeforeOod

/-- The selected callback imports the exact transcript representation extracted
from the same pinned `aspis-core` source through the R137 probe. -/
abbrev aspis_core.transcript.Transcript :=
  AspisR137Transcript.transcript.Transcript

end AspisR136BeforeOod
