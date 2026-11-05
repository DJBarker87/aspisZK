import NGX_SemanticRuntime
import Lean
open Lean Elab Command
run_cmd do
 let e ← getEnv
 for s in ["AspisR1PublicPreparation.PreparedHashCode.Code", "AspisR1PublicPreparation.PreparedHashCode.run", "AspisR1PublicPreparation.S1SemanticCode.sampleBlock", "AspisR1PublicPreparation.S1SemanticCode.newTranscript"] do
  logInfo m!"NGX_OWNER {s}: {(e.find? s.toName).isSome}"
