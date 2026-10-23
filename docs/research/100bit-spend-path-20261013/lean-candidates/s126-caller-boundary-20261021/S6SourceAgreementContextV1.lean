import S6FullSourceCodecV1
import S6FiveCodecStdOptionsV1
open Lean Meta Elab Term
/-- Elaborate only the type of an already checked source constant.
All generated context definitions and equalities are checked by the kernel. -/
elab "codec_type% " value:term : term => do
  let value ← elabTerm value none
  inferType value
