import NFY_Part005
open Lean Elab Command
set_option pp.fullNames true
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if s.endsWith ".atomic_statement.decode_digest_canonical" || s.endsWith ".AtomicStatementError" || s=="NFY_NBP_DigestDecode.result" || s=="NFY_NBP_DigestDecode.decoded" || s=="Aeneas.Std.core.cmp.PartialEq" then
   logInfo m!"FOUND {n}: {c.type}"
