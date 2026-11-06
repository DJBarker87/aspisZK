import NLG_COMBINED_IMPORT
import PCB_AppendRef.Funs
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for (n,c) in env.constants.toList do
    if "canonical_nullifier_encoding".isSuffixOf n.toString ||
       "digest_is_canonical".isSuffixOf n.toString ||
       "solana_sha256".isSuffixOf n.toString then
      logInfo m!"PCB_SHARED {n}\nTYPE {c.type}\nVALUE {c.value? true}"
