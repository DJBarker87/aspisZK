# Resume4 final live status

Branch codex/pv-cb-20261026; starting revision ff8096896d.
Rows23/73 →23/73 ROW-DISCHARGED(candidate). Endpoint premises removed0.
Target not yet established. No checked counterexample to a shipped source-row
statement was found. No shipped Rust/ELF/pin, endpoint observer, simulator,
existing hypothesis or published PV_CB statement was changed.

## What passed

- Actual extracted op223 caller transport on length16 slices, complete Result.
- Canonical M31/tower arithmetic, prepared multiplication, fill/update/linears,
  power26/Horner, and retained source/owned mask root numerical invariants.
- Generic compressor reference totality/canonicality and16-array specialization
  under explicit primitive source equations. Numerical canonicality differs
  from the already proved length16 domain; array producer canonicality remains.
- Extraction of a cfg-only copy of the actual tag expressions, importing their
  real shipped base constant; exact Result and tag<P for arbitraryu16 IDs.
- Three final joint audits:38404/38405/38406,64+134+28 declarations, all exit0;
  standard axioms only. Source hashes frozen and checked in the focused manifest.
  This is not a complete privacy release or full transitive-source replay.

## Budgets and native results

100/100 Lean attempts,77 passing and23 rejected/stopped. Seven preflights are
uncharged; IDs38300–38406 are all consumed. Next unused38407, but this run has
no remaining Lean budget. The final3 attempts were reserved for joint audits.
12/12 substantive Kani gates plus exactly3 configuration diagnosis probes.
The compiler failure was reproduced on a cold dependency-matched trivial
harness: rustc coordinator thread spawn WouldBlock/Os11. Four-CPU affinity
fixed that same cold probe within the third diagnosis, without changing caps,
shared launcher, toolchain install or sibling directory. Exact versions,
commands and logs: KANI-CONFIG.md. Initial small probe passed; five math gates
ran before the complete matched reproduction. This chronology is retained.

|Kani gate|exit|wall|GNU time RSS KiB|swap|revision|
|---|---:|---|---:|---:|---|
|kani-resume4-circle-001|124|3:00.00|15132|0|ff8096896df889d6f1ad5d467f59cf410275df7f|
|kani-resume4-compress16-001|124|3:00.00|15484|0|ff8096896df889d6f1ad5d467f59cf410275df7f|
|kani-resume4-compress16-canonical-001|124|3:00.00|15652|0|8a754e7607088a507a112e8192dd49f1a4c7b26e|
|kani-resume4-horner-canonical-word0-001|124|3:00.00|15484|0|228c7a22b3f622f6b955df9d22699599dfe80f48|
|kani-resume4-horner-canonical-word1-001|124|3:00.00|15304|0|228c7a22b3f622f6b955df9d22699599dfe80f48|
|kani-resume4-horner-canonical-word2-002|124|3:00.00|15304|0|228c7a22b3f622f6b955df9d22699599dfe80f48|
|kani-resume4-horner-canonical-word3-003|124|3:00.00|15304|0|21fd275d99247ee891415db284c47f7955e775f8|
|kani-resume4-pole1024-001|124|3:00.00|15136|0|8a754e7607088a507a112e8192dd49f1a4c7b26e|
|kani-resume4-power-canonical-word0-001|124|3:00.00|15656|0|21fd275d99247ee891415db284c47f7955e775f8|
|kani-resume4-power-canonical-word1-001|124|3:00.00|15480|0|b823593eb847175f89bbfd86b5102665e067a3d1|
|kani-resume4-power-canonical-word2-001|124|3:00.00|15652|0|5caf54e39440545f09b3b9c4694284edc7e039a7|
|kani-resume4-power-canonical-word3-001|124|3:00.00|15656|0|8a754e7607088a507a112e8192dd49f1a4c7b26e|

All12 substantive gates exited124 at180seconds; no verification verdict.

Attempt38300 was stopped by terminating its scope before GNU time flushed;
wall/RSS/swap are unavailable in that receipt. The retained sampled RSS and
source snapshot are not substituted for missing final metrics.

GNU time values for timed-out native gates are wrapper rusage, not an aggregate
CBMC/cgroup peak; no aggregate RSS measurement is invented. All gates enforce
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and optimized Rust. Each exact
target, revision plus proof input hashes, status and limits is in the named
collected receipt. Kani has no #print axioms; corresponding Lean audits are
separate. A timeout supplies neither a verification verdict nor a counterexample.

## Open rows and before/after

RESUME4-ROWS.md gives op→row→status→theorem→receipt. V240/op223 still lacks
PV_CB_Op223Source.op223_source; direct current Aeneas fails closed with escaping
reference output requiring loan validation. V217/op117 remains PARTIAL;
reference/control equality and numerical invariant lemmas do not bind fresh
shipped control. V265/op259 remains OPEN after the configuration fix: full
native circle equality has no verdict. V264/op258 remains OPEN: bounded pole
reference comparison supplies no source law. Other upward rows retain the
previous exact extraction obstructions; native erasure/fence/time/thread/file
world effects stay DEFERRED to pv-runjoin, with reasons in RESUME4-ROWS.md.

All prior source row statements and endpoint premises are unchanged. New helper
input invariants are local theorem premises, never additional endpoint premises.
Model-only arbitrary-dictionary obstruction is explicitly not a source-row
counterexample. PROPOSED-Op223CanonicalDomain.lean.txt is uncompiled and excluded
from every checked claim. One accidental overlap of Kani gate7 and Lean38391–393
violated the one-scope rule; RESUME4-SCOPE-DEVIATION.md records it. Subsequent
scopes were serial. No cap was raised and no failed gate was rerun unchanged.

## Retention and next deliverable

77 accepted Lean objects remain in this job's own lean-objects cache with hashes.
Only the three own disposable Rust target directories are removed after gates;
pinned tools, source, proof/evidence and Lean cache remain. No keys were created,
modified or deleted. The original unrelated codex-pv-cb2.out.run0 is untouched.

Next concrete deliverable is the stable PV_CB_Op223Source.op223_source from a
supported iterator/reference extraction, or a complete canonical-domain P6
association with the actual16-value producer invariant. Then let rw21 consume
the final V164 source hypothesis; that endpoint premise is not removed here.

## Commits since the starting revision

```
8a754e7607 Audit joint candidate and helper axioms with final reserved attempts
5caf54e394 Prove compressor reference domain invariants and freeze focused joint audit
b823593eb8 Prove canonical mask reference invariants and reproduce Kani thread failure
21fd275d99 Prove compressor caller transport and current canonical arithmetic invariants
228c7a22b3 Record compressor callback boundary and isolate Kani compiler configuration
```
