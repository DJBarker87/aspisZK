# Reusing the completing decoder for semantic rows 1–25

One generic theorem now covers every ordinary semantic row `0 < n < 26`.
The decoder uses the public bytes, queried address and table before that
address. It does not receive the oracle, proof, actual transcript, or round
number. Its parser recovers C1 and earlier records, checks the current indexed
message, and accepts only recovered record counts from 1 through 25.

`UnifiedSemanticCase.decodes_and_follows` proves that, on the actual
prover-then-verifier experiment, this decoder returns the actual protocol
prefix, message and challenge. The theorem retains the first-read budget,
duplex collision exclusion, public-byte length bound, and row-zero codec
premises. Earlier prover queries are included in the trace and budget.

## Exact reuse

| New connection | Existing checked machinery reused |
| --- | --- |
| Earlier records have known absorb cells and observed squeeze reads | `DuplexRecordPrefix.table_cells`, `UnifiedPrefixedReads.ordinary_reads`, `UnifiedSteps.state_step` |
| Recover the typed prefix and canonical indexed current message | `UnifiedSemanticRecovery.typed_before_row`, `InitialWalkTrace.walk_before_next`, `RawRoundCompletion.decode_records`, `IndexedMessage.read_encoded` |
| Fill missing answers and follow the current round | `PrefixPendingFacts.pending_facts`, `QueryOwnFollow.follow`, `TraceSuffix` facts, `PrefixAnswers.fromAnswers_map` |
| Recover the exact transcript representation | `UnifiedRecordCompletion.completed_eq_transcript`, `UnifiedRecords.ordinary_challenge` |
| Obtain the completing sampler law | `BackgroundLawMap.blaw_map`, `PrefixNextLaw.background_law`, `UnifiedSampler.unified_law` |
| Connect the actual experiment to the existing protocol interface | `FS.experiment_eval`, `FS.eval_consistent`, `UnifiedProtocol.transcript_eq`, `UnifiedProtocol.chal_eq` |

The older machinery is applied without changing its theorem statements or
proof bodies. The new work supplies the premises and representation equalities
needed for this particular transcript. For example, a record's absorbed state
is proved to be the value of an earlier table cell; it is not assumed merely
because parsing produced a record.

`PrefixNextTrace.follows_after_prefix` is reusable beyond this range. It takes
explicit known-cell and read facts, derives freshness and disjointness of the
pending answers, and applies the existing suffix-following theorem. The
semantic injection theorem discharges those facts from the actual run.

`UnifiedSemanticContext.parse_sound` exposes the successful absorb parser,
typed recovery and indexed message read. `IndexedMessage.read_sound` then gives
the expected label, successful abstract decoding and exact re-encoding.
This is canonicality in the abstract message codec, not yet a refinement
proof for the Rust byte/field parser.

## Probability boundary

`UnifiedSemanticLaw.background_sampler_law` equates the completing sampler's
law to a background average of the existing unified fresh sampler, at the
recovered round and completed prefix. `decoded_bound` transfers an explicit
fixed-prefix bound through this equality. Neither theorem invents that bound
or asserts independence for an arbitrary oracle trace.

The full address-only dispatch still needs to select the correct component
without an oracle-dependent round argument. The reseed row 26, opening rows
27–30 and query row 31 remain to be connected as decoder cases. Initial row 0
and final row 32 were connected in the preceding endpoint checkpoint.

The full `Inj3`, D1/D2/D3 and numerical Fiat–Shamir instance remain open.
The generic bound still charges `Qtot * maxErr` and collisions; this change
does not remove the query factor or establish a complete 100-bit claim.
The concrete Rust/account/settlement correspondence and universal masking
simulator argument also remain open.

## Verification

Ten focused targets, including one final combined checkpoint, were checked
on the NUC using the pinned cache and 4G/6G/0-swap cgroup limits. The combined
checkpoint passed once after its dependencies, in 1.41 s at 3,528,532 KiB peak
RSS, zero swap. Its fifteen axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The sealed evidence is in
[`evidence/lean-unified-semantic-20261014`](evidence/lean-unified-semantic-20261014/README.md).
It preserves every attempt's source hash, exact source, receipt, compiler log,
wall time, peak RSS and swap, plus the final compiled-object archive and
runner/environment. Root reviewed the theorem premises and the final source
connections. These Lean additions do not change the runtime artifacts.
