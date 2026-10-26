# Source-identification result

Branch `codex/pv-srcid-20261026`; base `322afc54f7` (`research` recount).
**Target not yet established. No V152–V154 native endpoint row removed.**
No frozen implementation, headline, observer, simulator, or release pin changed.

| Row | Status | Validated theorem | Receipt |
|---|---|---|---|
| V152 public_eq | REDUCED | `R1Z.PV_Src_NativeIdentification.public_eq` | attempts22676/22689 |
| V153 build_eq | REDUCED | `R1Z.PV_Src_NativeIdentification.build_eq` | attempts22676/22689 |
| V154 transport_eq | REDUCED | `R1Z.PV_Src_NativeIdentification.transport_eq` | attempts22676/22689 |

`NativeIdentification.identification` constructs the original structure for
actual returned `compile_forest_from_copies` columns. `ForestCompilation.returned_bank`
22675 proves the internal returned-column association from successful source
execution. `NativeConsumer.builder_premises` / `phased_builder_premises`22677 use
the unchanged original consumer type. The fixed headline's model theorem is
unchanged; actual deployed prover/RunJoin installation remains open.

Before/after equations, quantifiers and five exact native premise families are
in [STATEMENTS.md](STATEMENTS.md) and the type print in [out-22689.log](out-22689.log).
The five fields are `compile_call`, `words`, `publicCorr`, `admission`, `row_call`.
These retain nested WitnessOk(3fields), PubCorr(7fields), original Rspend plus
sentinel, and existing ExternalLinear/Records callback parameters. No full
trace-equality premise is hidden in the source definition. Callback native
association remains open; a standard-axiom proof does not discharge it.

The generic canonical encoding certificate (`ForestCanonical.identification`,
22632) is constructed. Both canonical release fibres are inhabited and have
actual extracted bank/column stage success (`Fixtures.fibres/fixture_run`,22662).
Full native release-fixture non-vacuity, successful native compile_call and
V047 byte association remain **OPEN**; stage fixtures alone do not meet them.

Validation:100/100 charged Lean attempts,68 successful,32 failed diagnostics;
reservation refusals charge zero. All current PV_Src module hashes match
successful attempts ([final-lean-source-audit.json](final-lean-source-audit.json)).
Final focused closure audit22689 passed2.17s, peak RSS4,223,404KiB, swaps0,
source revision19d452f549; only propext/Classical.choice/Quot.sound. Every attempt
records exact source/object hashes, revision, wall/RSS/swap/caps and axioms in
[attempts.jsonl](attempts.jsonl). One final focused closure audit was run; no
full frozen release manifest replay is claimed. Generator --check and source
scan passed. No new axiom/sorry/admit/native_decide or raised proof options.

The value-bit and private-direction helpers are proved against actual extracted
local functions (22682/22683/22687). They do not replace the full native record
and admission obligations. Failed reduction approaches/receipts are retained;
no unchanged killed job was rerun at a larger cap. Shared own-source/object
snapshots are hashed before API replacements; required own consumers rebuilt.

Kani gates are still running; final results will be recorded below. Historical
unstubbed row evidence is reused only for byte-identical selected functions,
as documented in transport-reuse.json. New gates are source validation under
Kani/CBMC trust, not Lean kernel proofs or release-binary association.

Next concrete deliverable: extract/associate native Records and external-linear
callees, instantiate all five native premise families and full compiler runs
for both real release fixtures, then install the source certificate into the
actual deployed RunJoin/headline path and replay the frozen closure.

Proof-stage commits (before this report commit):

```text
1ab2e984e7 Audit native source certificate and prove extracted bit helper behavior
19d452f549 Prove source identification for successful extracted forest compiler returns
3aa0be181c Validate both source stage fixture fibres and isolate compiler control flow
4517536926 Type the native compiler boundary and connect the unchanged builder consumer
6aaa34be2b Port bank refinement to the forest source with a fixed-prime invariant
70a3f99370 Prove total extracted stages and construct canonical source identification
840fced0fd Prepare actual coefficient wrapper gate and audit prior transport pins
fbf9d252a1 Resume source stage proofs and make remaining associations explicit
71d9b75ad4 WIP snapshot before capacity relaunch (auto 0)
1508d64ce5 Record source identification statements and extraction boundaries
```

Kani resource interpretation: the `dev/unoptimized` line describes Kani's
verification compilation. There is no long native Rust elimination, field
arithmetic, or proof generation running in a debug executable; the heavy step
is the installed optimized CBMC symbolic checker. Its binary/tool hashes are
recorded per run. No function replacement or verification stub is enabled.
