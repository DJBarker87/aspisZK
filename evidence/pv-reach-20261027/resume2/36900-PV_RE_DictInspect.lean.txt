import R1Z.ProverRwFullFuns
open Lean Meta Elab Command
run_cmd do
  for n in [`ProverRwFull.prover.prove_masked_attempt, `ProverRwFull.prover.retry_attempt, `ProverRwFull.host_semantic.check_secure_column_loop] do
    let c ← getConstInfo n
    logInfo m!"TYPE {c.type}"
    if let some v := c.value? then
      logInfo m!"VALUE {v}"
