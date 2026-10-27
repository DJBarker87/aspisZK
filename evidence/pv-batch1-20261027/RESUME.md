# Resume under LOG D282 / ruling (l)

User-authorized resume from a964ac5c61. Source repair ccf87ccecd restores
weights.rs exactly to c57a344726; its op254 indexed body now lives in
cfg(prover) prover_powers.rs. Only prover.rs and sim.rs direct calls redirect.
See MODULE-GATES.md and revised-applied.diff. No other shipped-code changes.

Admission for stage transfer passed at 12:28:32 UTC. The immediate default
build reservation refused at 12:28:39 (reserved 59,995,324,416 bytes plus 8 GiB
above the 55 GiB safe limit); no scope started. Retry after 12:31:39 UTC.
No Lean attempt or env-J ID consumed. Shared env-J sources remain untouched.

The existing extraction draft now selects prover_powers.rs for op254.
Extraction and proof work are dependent on all three ELF pins passing.
Target not yet established; all callback/endpoint obligations remain open.

The first retry was sent at12:31:35 UTC, four seconds before the required
12:31:39 deadline. It also refused before a scope started. This was a wait
policy deviation; next retry is no earlier than12:34:35 UTC (three minutes
after the fresh refusal). No compile ran and no cap was bypassed.

Gate (a) default passed on retry4 at source ccf87ccecd: exact f8c0ec72…,
1,563,728bytes; exit0,41.435s,peak686356KiB,swap0. Devnet passed:
exact63ad3e9c…,1,563,728bytes; exit0,50.679s,peak685640KiB,swap0.
Pool is the remaining gate. No extraction or Lean scope started yet.
Retry3 refused at12:38:07 UTC with51,405,389,824bytes reserved; retry4
admitted after the next full wait with34,225,520,640bytes reserved.

Pool passed: exact121f3e29…,605704bytes; exit0,39.930s,peak678204KiB,swap0.
All three gate(a) pins passed; gate-a-resume.json contains the complete receipts.

Fresh extraction began after admitted staging retry1. Op230 Charon and
pinned Aeneas completed; op254 Charon completed. Op254 Aeneas admission
refused before a scope, so the task driver waits three minutes and retries
only Aeneas with a fresh label; it does not rerun the successful Charon phase.
No Lean compile or ID consumed at this point.

All three fresh extractions passed. See extraction-resume.json and the
verbatim generated-*/ directories. backend-ports.json records the import
renamings, two positive31 literal ports in254, and literal4/masked-count
ports in258. They are not yet Lean checked. No shared env-J sources written.

Lean attempt53600 failed before elaboration: the private-root adapter removed
J/objects from the first namespace search position, exposing a partial Aeneas
namespace in commit54/objects. The complete Aeneas.olean exists in J/objects
(sha d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d).
Correct the task-private adapter to keep private objects first and J/objects
second, preserving the standing launcher's shared namespace priority. Only
the task-private env/launcher change; shared env/launcher/sources stay untouched.
Fingerprint the environment as well as dependencies. The changed environment
justifies retrying the unchanged small lemma with next unused53601.
53600 charged1/100: exit1,0.170s outer wall,190948KiB peak RSS,swap0; no
#print axioms output because import resolution failed before elaboration.
