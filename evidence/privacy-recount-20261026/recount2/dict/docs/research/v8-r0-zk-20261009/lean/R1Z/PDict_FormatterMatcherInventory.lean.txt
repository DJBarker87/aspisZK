import R1Z.ProverRwFullFuns
open Lean Elab Command
-- Read-only generated-matcher inventory for the isolated retyping obstruction.
run_cmd do
  let env ← getEnv
  let matcherPrefix := "ProverRwFull.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible.match_"
  for (n, _) in env.constants.toList do
    if matcherPrefix.isPrefixOf n.toString then
      logInfo m!"MATCHER {n}"
