# Preflight failures without prover invocations

These are retained diagnostics, not counted as Lean/Kani executions:

- The first dependency shell used `seq -w` and shell `printf %03d` interpreted08
  as octal: `printf: 08: invalid octal number`. It attempted PoolT_L000.json;
  existing launcher raised FileNotFoundError before Lean. Corrected shell to
  unpadded seq, then continued with L008. No launcher/tool was modified.
- An initial local K005-source preparation raised ValueError substring not found;
  rsync lacked PoolT_K005.json, and the attempted launcher raised FileNotFoundError
  before Kani. Corrected local source preparation; actual K005 is the separately
  receipted Bitwuzla parser failure. No Kani invocation was concealed.
- L055 existing lean launcher raised FileNotFoundError: PoolT_Snapshot before
  Lean started because its prerequisite was not yet green. Fixed the prerequisite
  first (L056), then changed child source L057. Count60 Lean submissions,
 59 actual Lean invocations. This dependent-before-green scheduling mistake
  is retained; the failed child was not treated as checked.

No infrastructure repair, new launcher, cap increase or timeout bypass occurred.
