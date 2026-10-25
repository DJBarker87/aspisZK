/- UNCOMPILED, deliberately closed admission gate. No project trust import.
After review, replace ONLY this gate with a pinned plan reader, full exact-name
selection/group/core-axiom guards, ordinary Port30JOIN_Kernel replay, and final
strict readback of every selected ConstantInfo. RawSession and all regions must
stay alive until process exit, including every later theorem/axiom audit.
Do not free them after setEnv; the checked environment contains their Exprs.
No authorization is implied by importing this module. -/
import Lean
import Port30JOIN_Select
import Port30JOIN_Kernel
open Lean in
run_elab do
  throwError "Port30JOIN disabled: exact-name selection, raw missing bodies, notation/API and fresh compiler allocation require lead review"
