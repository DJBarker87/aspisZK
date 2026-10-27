# pv-srcid3 second resume

Branch `codex/pv-srcid3-20261026`, resume base `34995987c0`, original branch base
`52a0f8acee`. No push or merge. Target not yet established.

The original missing-object inventory is **92 → 0**. All 92 named modules
were rebuilt as charged attempts, dependency first, through the unchanged
restored launcher. Sources came from pinned research `026ce6502610244e2f819d8cfd027c72ee03b572`
where present (53); the other 39 are explicitly unmerged branch additions.
Successful outputs were copied byte-for-byte into the reused task's own
lean-objects directory; the launcher's fixed shared output path was also
refreshed, as documented in RESUME5.md. No launcher or environment was changed.

**Full kernel audit PASS; merge byte-provenance gate BLOCKED.** Initial
FinalAudit 36302 covered 129 PV_Src modules and 575 standard axiom reports.
After three new modules and the final extraction import/name correction,
FinalAudit 36309 covered **132 modules, 553 theorem declarations, 579/579
standard reports**. Only {propext, Classical.choice, Quot.sound} occur.
The second replay had changed sources/dependencies; it was not an unchanged
regression. No complete unrelated release manifest was rerun.

The expanded cross-root inventory has 839 project modules plus 193 external
import roots, **zero missing enumerated objects**. The known material host
source mismatch is `R1NaturalProjection`: actual SHA
`add9c506d5cbf5c55447c9df156a52eb2298fe5ecf53faff2ea6a9654152726a`,
research SHA `41db583fe5032f1d5ca0757d98da80d34f6949983599d369560eaa3574c5a368`.
Its evaluator/API differs, so the soundness-algebra dependency was neither
rewritten nor silently accepted. Actual source and full diff are retained in
unaccepted-external-sources/ and the source-diff receipt. Forty-six further
research-source copies are absent from the joint source tree, and exhaustive
package-source/object provenance is not claimed. All selected repository
sources that exist on research match their pinned Git bytes; 64 new branch
sources are separately pinned. Exact resolved objects, source alternatives,
missing-source-copy names and gate reasons: resume5-final-full-closure.json
and resume5-final-gate.json. Final selected-source comparison to research `b6c61840f519872fc9464824cf15956fa5d9fbf6` finds no changes to existing source selections; 64 branch additions remain absent there. Kernel success is not a substitute for this gate.

## Accepted proof changes

- `PV_Src_CanonicalPrivateRecord.{witness,admission}`: the corrected combined
  bridge now compiles, covering transfer and withdrawal after canonical
  normalization. Admission retains the exact returned-public/canonical-public
  equality; arbitrary compiled payloads are not asserted successful.
- `PV_Src_DynamicAdmission.selected`: carries that admission theorem through
  the actual dynamic reference's successful record result, for every returned
  root table. The public association remains explicit.
- `PV_Src_DynamicPublic.correspondence`: dynamic reference PubCorr follows from
  full compiler success, canonical snapshot frontier and the single actual
  pure `pair_empty_roots = ok PV_Src_CanonicalRoots.table` equation.

All 64 new/changed formal files since the original branch base match successful
source receipts and contain no forbidden proof constructs. DynamicSource
remains only an uncompiled draft; it receives no accepted-result credit.

## Exact family boundaries

| Family | Status and retained interface |
| --- | --- |
| compile_call | OPEN: `∀ i, PV_Src_NativeInput.run (inputs i) = ok (.Ok (inputs i).compiled)`. The actual pure `BuilderForestAdmissionPort.Records.call` source equation is still owed under D188; no effect assumption replaces it. |
| words | REDUCED to full unstubbed shipped mapper equality with `PV_Src_RecordDynamic.dictionary`, plus the installed checked canonical input selection. The checked/reference theorem is proved; no new shipped P6 equality is credited. |
| publicCorr | REDUCED to deployed snapshot/public/root association. `DynamicPublic.correspondence` states the remaining actual root-helper equation explicitly; it does not prove it. |
| admission | REDUCED to the published `PV_RunJoin_SourceSelectionContract.selectedRecord`/public binding and `PV_RunJoin_SelectedAdmission.Remainder.admission`, with the same selected records. New canonical/dynamic lemmas retain the exact publicEq join. |
| row_call | REDUCED to `PV_RunJoin_InstalledTransport.endpoint_row_call` at the exact endpoint, with `PV_RunJoin_NativeSelectedInputs` preserving the selected compilation. No foreign branch installation is inferred. |

Actual deployed **PV_Src_Premises 5 → 5**; zero endpoint fields discharged,
added, renamed or weakened. The existing fixed-root reference Remainder stays
3. The unchanged `PV_Src_ThreeConsumer.builder_premises` consumer and both
fixture canonical fibres/primitive record-and-bank stages passed the complete
audit. Full compiler-success/installed fixture fibres remain open. Neither
primitive-stage non-vacuity nor smaller conditional consumer type establishes
a full deployed smaller instance.

The four requested RunJoin interfaces were read using git show. They are
byte-identical between the initial and final pins despite branch advancement;
final pin `bb493b62e71686f03c2bf33884a899f73b0eadfb` and full source hashes are in resume5-runjoin-final-pin.json. There
was no foreign worktree edit or merge.

## Receipts and budgets

All **100/100 Lean attempts** succeeded, one scope at a time, -M7000,
MemoryHigh=6G / MemoryMax=8G / swap0 / TasksMax=64. Maximum Lean RSS was
4,239,876 KiB; all swaps zero. Refusals were uncharged, waited at least three
minutes, and consumed fresh IDs. Next unused Env-J ID: 36310; Lean budget zero.

| ID | Target | Exit | Wall | RSS KiB | Swap | Revision | Axioms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 36302 | PV_Src_FinalAudit | 0 | 2.20 s | 4234376 | 0 | 9b3806cc36 | 575 standard |
| 36303 | PV_Src_CanonicalPrivateRecord | 0 | 1.66 s | 4106396 | 0 | fb141d0105 | 163 standard |
| 36305 | PV_Src_DynamicAdmission | 0 | 1.54 s | 4100780 | 0 | 2eeb4408ec | standard |
| 36306 | PV_Src_DynamicPublic | 0 | 1.75 s | 4103568 | 0 | 2eeb4408ec | standard |
| 36309 | PV_Src_FinalAudit | 0 | 2.38 s | 4229844 | 0 | 639a67e175 | 579 standard |

Targets have prefix R1Z/. `resume5-attempts.jsonl`, RESUME5-RECEIPTS.md and
out/time/sha-ID files contain every exact target, exit, wall, peak RSS, swap,
revision, source SHA, imported object hashes and full printed axioms/errors.
Three extraction source variants were rebuilt only with research import/name
bytes; their prior shared source/object snapshots are hash-recorded.

All **6/6 Kani invocations** completed with verification timeouts (180 seconds
each). No unchanged timeout was retried. The six transfer/withdrawal ×
fields/path/public splits execute both actual dynamic mappers without stubs;
generated metadata confirms stubs=[], verified_stubs=[], unwind33 for all six,
and commands enable unwinding assertions. There is **no new P6 equality result**
and **no checked ROW counterexample**. Actual compiler fingerprints confirm
opt-level=3, mir-opt-level=4 and MIR inlining. Heavy time was CBMC verification
after compilation, not unoptimized arithmetic. The maximum cgroup memory peak
was 2,797,080,576 bytes; all swaps were zero. GNU time's timeout-process RSS
does not aggregate all CBMC descendants; its raw numbers and the stronger
full-scope cgroup memory measurements are distinguished in
RESUME5-KANI-RECEIPTS.md. No exact aggregate peak RSS is invented.

All six scopes are inactive. No identifiable owned solver temp file was found
in the recorded /proc FD scans; unrelated /tmp files were not deleted. The own
Rust target cache and Lean output scratch were removed under the disk-hygiene
rule after hashing and checking the shared copies. Source, prior replacement
snapshots, metadata, receipts and all shared current Lean objects are retained.
Ninety-eight own object copies matched the shared bytes at bulk cleanup; one
early client (BankRange 36213) raced the retention-hook correction and was
subsequently copied/hash-checked against its dependent receipt, then cleaned.
This late retention recovery charged no compile and is recorded separately in
resume5-late-own-retention.json. No key filename candidates were found.

One snapshot timing deviation is retained in RESUME5-SNAPSHOT-CORRECTION.md:
the initial shell quoting failed to make pre-replacement copies. All seven
pre-existing source/object pairs were recovered later against the preflight
hashes, with identical original bytes; no pre-existing byte content was lost
or changed. The command was corrected before replacing the three differing
extraction variants. Post-hoc recovery is not presented as a pre-run snapshot.

No shipped source under crates/ or programs/ changed. The new Rust code is
inside the existing cfg(kani)-only harness module. The prior poseidon proof
has its own cfg(kani), and records/empty-roots children inherit the cfg(kani)
records_proofs parent. No ELF rebuild or pin change is claimed. No wallet key
was created, removed or destroyed. No observer, simulator or headline target
was weakened. L1/L2/L3 and all remaining deployment conditions remain retained.

Stopping reason: **both new allocations exhausted**, not an infrastructure
refusal, an unproved equation treated as false, or a changed privacy target.

Next concrete deliverable: the lead must reconcile/approve the exact
R1NaturalProjection source profile and complete the missing source/object
provenance attestations before merge. Then prove the pure Records source
equation and actual empty-root recurrence symbolically, finish the unstubbed
mapper association, and install the exact RunJoin selected-input/public/
transport joins with both full fixture fibres inhabited. The current
conditional source joins do not remove a deployed endpoint premise.
Target not yet established.


Previous exhausted allocation: REPORT-srcid4.md. Full branch history is in
COMMITS.txt; the final handoff commit follows its captured history.
