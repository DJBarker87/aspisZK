# V197 owned-model consumer inventory (D570)

Snapshot: [REFS-before.txt](REFS-before.txt), 106 local/remote refs plus the
pinned HEAD, 77 distinct revisions. [CONSUMERS-census.json](CONSUMERS-census.json)
links the literal `git grep` outputs and reverse import closures. Search covers
all tracked Lean, Python, Rust and shell sources. Empty grep files are negative
results, not omitted branches. The local and remote candidate refs are included.
No fetch, checkout, merge, push or write to any other worktree occurred.

The model is `PV_RDCD4_BytesSource.{scalar,component,cm,qm}`. We also census its
old shared range helper so that V236 is not missed. Modules below are the union
across all refs, including uncredited drafts and audit-only users. Branches with
these modules: pv-c474-draft, pv-fmtaudit, pv-meas, pv-open11, pv-rdcd4, pv-rdcd5,
pv-runjoin and origin/cx-prover-rw (full names/revisions in the JSON). All other
pinned refs return no matching source consumer.

| Consumer (R1Z unless tools/) | Failure KIND or success/failure only? | Credit and recheck disposition |
|---|---|---|
| PV_RDCD4_BytesSource.scalar/scalar_binding | No failing branch; unchanged | Scalar/endian local law, credited; recompile unchanged scalar with corrected parser |
| PV_RDCD4_BytesSource.component/cm/qm | Complete Result; inherited erroneous range constructor | V197 owned draft, no source-association restoration; corrected in place to parser-specific panic range |
| PV_RDCD4_ParserWindows.component_window | Bounded success windows, no error-kind inspection | Uncompiled/uncredited draft; recheck corrected components |
| PV_RDCD4_ParserWindows.compose/no_write | No parser result dependency; no_write is bounded old-helper success | Local draft; unchanged helper law, focused recheck |
| PV_RDCD4_V197.source_reference/short_failure/frame | **KIND**: explicit arrayOutOfBounds in reference and short_failure | Uncompiled/uncredited V197 draft. Correct to panic, using rdcd5's already established bind-congruence proof repair |
| PV_RDCD4_FinalAudit | Imports model; only queries scalar_binding and generic range lemmas, not qm/cm or V197 draft | Audit credit only; affected declaration queries rechecked in focused V197 audit; unrelated rdcd4 row checks retained historically |
| PV_RDCD4_FocusedReplay | Transitive import of FinalAudit; v201/v220/v237 do not call parser | No failure-kind dependence; their source/dependency cones unchanged |
| PV_RDCD4_FrozenManifest | Transitive audit/replay imports, no parser execution | No failure-kind dependence; scoped declaration projection suffices, no unchanged full-suite rerun |
| PV_RDCD5_ParserWindows.component_window | Bounded success windows, no error-kind inspection | Credited local owned-model proof; recompile corrected components |
| PV_RDCD5_ParserWindows.compose/no_write | As rdcd4 variants above | Credited local laws, recheck |
| PV_RDCD5_V197.source_reference/short_failure/frame/slice_instance | **KIND**: explicit arrayOutOfBounds, arbitrary-input complete Result equality | Credited as local owned-model proofs only, **not** restored V197. Explicitly corrected to panic and rechecked |
| PV_RDCD5_ParserFlat.cm_window/cmAt | Complete Result equality, both bounded component windows; no error-kind inspection | Credited local model law; recompile against correction |
| PV_RDCD5_ParserErrors.existing_empty | **KIND**: source panic, does not use owned model | Credited diagnostic, unchanged source result |
| PV_RDCD5_ParserErrors.owned_empty/carrier_mismatch | **KIND**: arrayOutOfBounds and inequality on empty input | Credited **V197 FINDING**, not a restored source law. Historical result remains in rdcd5 receipts at its pinned revision; corrected model gives owned_empty=panic and new carrier_agreement. Old mismatch declaration removed explicitly, not silently reinterpreted |
| PV_RDCD5_FinalAudit | scalar/range/owned-parser proof queries; includes kind-sensitive ParserErrors and V197 proofs | Audit consumer; stale mismatch query changed to agreement. Scoped full-type/axiom projection rechecks affected entries |
| PV_RDCD5_FocusedReplay.v197_finding | **KIND**, empty-input inequality | Credited V197 diagnostic replay; renamed v197_corrected and changed to equality, with before/after retained in git diff |
| PV_RDCD5_FocusedReplay.v233/v236 | No owned parser calls; transitive audit import only | Restored V233/V236 laws unchanged; no result-kind dependence |
| PV_RDCD5_FrozenManifest | **KIND** through querying v197_finding | Audit consumer; explicitly query new v197_corrected; new V197 frozen manifest will replay corrected exact association |
| PV_RDCD5_BufferSource | Uses shared SliceRange194, **not BytesSource**; all ranges bounded success in cursor_transport/finish_binding | Restored V236 supporting law. Shared helper unchanged; no correction dependency, no wrong-kind credit |
| PV_RDCD5_V236 | Transitive BufferSource, no BytesSource/parser dependency | Restored V236; no wrong-kind dependency, unchanged |
| tools/pv-rdcd4-20261029/prepare-final-replay.py | Generates import/axiom-query text, no parser execution or failure branch | Historical audit generator; no wrong-kind source-law credit |
| tools/pv-rdcd5-20261101/prepare-audits.py | Generates parser diagnostic queries (therefore old KIND-sensitive query names), not runtime semantics | Historical generator is evidence for old run, not rerun; replaced by scoped current audit generator |
| tools/pv-rdcd7-20261102/consumers.py | Searches model names only | This census, no semantic credit |

**Immediate report to lead:** V197's old local `short_failure` statement and
its credited empty-input diagnostic/replay depend on the old failure kind.
V197 was FINDING/SUSPENDED, never restored. No restored consumer has been found
to depend on that wrong kind. Correction supersedes the diagnostic for the new
model; it does not erase the historical counterexample. No new security-row
finding beyond V197 is presently identified.

Recheck results are provisional until the focused receipts and final audit are
complete; this inventory does not itself claim compilation.

New consumers introduced by this correction (on this branch):

| Consumer | Failure-kind dependence | Verification target |
|---|---|---|
| PV_RDCD5_ParserRange | Complete Result, literal panic; uses old helper's window only | binding on every Slice/Usize range |
| PV_RDCD5_ParserComponent | Complete Result and literal panic; typed conversion/residual adapters | component_binding, residual_none, first_bind, second_bind |
| PV_RDCD5_ParserTransport | Complete Result, every panic/None/Some; typed component/CM/QM transport | component_binding, complex, quartic |
| PV_RDCD5_V197Restored | Complete Result and actual checked borrowed windows | parser_instance, native_window, input_frame, rdcd4_instance |
| PV_RDCD5_V197ConsumerReplay | KIND: corrected empty-input equality; exact corrected replay proof | v197_corrected |
| PV_RDCD5_V197Audit / V197Focused / V197FrozenManifest | Full declaration-type/axiom queries, including KIND-sensitive statements | affected-consumer audit, focused, final manifest |
| PV_RDCD5_NEPDriver | Dynamic root/constant-graph audit, no parser execution or error erasure | fixed full-private-data raw walk |
| tools/pv-rdcd7-20261102/parser-source.py | KIND: asserts panic and all three migrated calls | structural schema plus explicit syntactic mutation controls |
| Other new census/staging/receipt tools | Source names, hashes and query inventories only | source/fingerprint checks, no parser result credit |

Historical `SliceRange194.index` retains its old model error tag. The parser no
longer calls it. No universal native failure-kind credit is claimed for it;
V236 uses bounded success windows. The corrected parser's faithful helper has
a complete, proved Result binding.

Session 3: user confirms sole writer and accepts continuation of the committed
ParserComponent split. RESUME-SESSION3.json verifies all host receipts; no live
scope or driver remains. 16 Lean and 2 native spent; 90716 unlaunched.

The session-3 live-ref refresh (CONSUMERS-session3-refresh.json) covers 15
additional revisions against the original census. All new model variants are
on this task branch or its remote ref; no other advanced live ref adds a
consumer. The exact grep results are retained in session3-census/.
