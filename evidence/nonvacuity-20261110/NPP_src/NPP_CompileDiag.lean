import NPP_ComputableModel
/-! NPP_ diagnostic: why the copy NPP_C.LIB_VLib.library (and so tx1Value) has no code.
Recompiles a few copies with compiler errors reported, and lists the noncomputable constants
their values mention. -/
open Lean Meta in
run_meta do
  for n in [`NPP_C.LIB_VLib.library, `NPP_C.LIB_Prepared.child, `NPP_C.LIBC_BatchMerkle.model] do
    let some ci := (← getEnv).find? n | IO.println s!"NPP_DIAG {n} missing"
    let some v := ci.value? | continue
    let env ← getEnv
    let nc := v.getUsedConstants.filter (isNoncomputable env ·)
    let noIR := v.getUsedConstants.filter fun c => (Lean.IR.findEnvDecl env c).isNone &&
      (match env.find? c with | some (.defnInfo _) => true | _ => false)
    IO.println s!"NPP_DIAG {n}: noncomputable deps {nc.toList.take 12}; defs without IR {noIR.toList.take 20}"
    try compileDecls #[n] (logErrors := true) catch e => IO.println s!"NPP_DIAG compile {n}: {(← e.toMessageData.toString).take 900}"
