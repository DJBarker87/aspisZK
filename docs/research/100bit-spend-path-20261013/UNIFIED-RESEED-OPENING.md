# Reseed and ordinary opening decoder cases

The completing decoders now recover and follow row 26 and rows 27–30 on
the actual prover-then-verifier experiment. Both use only the public input,
queried address and table before that address. They recover their round
from the parsed record count, without receiving an oracle or proof.

| Rows | Checked connection |
| --- | --- |
| 26 | Semantic-prefix recovery, current message, challenge and extra P3 reseed hash |
| 27–30 | Prefix recovery across initialization and P3, current message and ordinary challenge |
| Before 31 | Typed prefix, known absorb cells and squeeze-read facts; the query-round completing decoder remains separate |

## Keeping the reseed in the transcript

The input prefix at row 26 has 26 earlier records. The current challenge is
sampled from the current absorbed state's squeeze hash. The next state is
the output of P3 applied to the advance hash, rather than the advance hash
itself. `UnifiedReseedView.actual_output` uses the existing `reseed_step`
theorem to preserve that distinction.

`ReseedOwnFollow.follow` applies the existing `bfollow_ok` theorem with
explicit pending-answer freshness and four own-sampler addresses.
`PrefixReseedTrace.follows_after_prefix` discharges those premises: the old
duplex event orders the absorb before squeeze/advance; the already charged
tail-state event orders the advance before P3. The pending answers are
squeeze addresses of length 33, so they cannot alias the length-62 P3 frame.
The earlier records are completed using the existing `PrefixAnswers` map
and `PrefixNextLaw.output_append` lemmas.

The row-26 parser is the previously checked semantic-context parser, guarded
by `records.length = 26`. `UnifiedReseedInjection` derives its successful
parse and trace following. `UnifiedReseedCase` supplies the exact protocol
triple on the actual experiment, including earlier prover queries.

## Recovery after the domain transition

`UnifiedOpeningRecords.ordinary_eq_records_any` generalizes the previous
fixed four-record list split to any opening length. This is a symbolic
list equality and asserts no valid transition beyond the protocol range.

`OpeningEndpointCells.cells_before_next` exposes the earlier semantic and
opening cells at the endpoint itself. `UnifiedOpeningRecovery.recover_before_row`
instantiates the existing opening walk and typed codec for `k ≤ 4`, before
row `27 + k`. It derives the exact typed prefix and the known-cell/read
facts required by the earlier `PrefixNextTrace` theorem. At `k = 4`, the
endpoint's read comes from the query sampler; no ordinary-row read is
assumed for row 31.

`UnifiedOpeningDecoder` checks the current indexed message and accepts
record counts 27–30. `UnifiedOpeningInjection` reuses `PrefixNextTrace`
without modifying it. `UnifiedOpeningCase` identifies the first cell and
returns the actual protocol prefix, message and challenge for all four rows.

## Sampling law and remaining scope

`UnifiedReseedLaw` reuses `ReseedSamplerLaw.background_law` and the unified
row-26 sampler law. `UnifiedOpeningLaw` reuses the earlier ordinary-prefix
background law and the unified ordinary sampler law. Their bound-transfer
theorems retain the fixed-prefix bounds as explicit premises.

The query-selection decoder case and correct global dispatch remain open.
Existing per-case results are not yet a full `Inj3` instance. D1/D2/D3,
concrete density/extraction composition and the numerical security instance
also remain open. The generic `Qtot * maxErr` factor and combined collision
budget remain present; no work or grinding credit has been added. These
theorems do not establish Rust/field/account/settlement correspondence or
the universal masking simulator required for privacy.

## Verification

Sixteen focused final targets were checked on the capped NUC. After their
dependencies passed, the combined checkpoint ran once in 1.38 s with peak
RSS 3,531,264 KiB and zero swap. Its 24 axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`. Every job used MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0 and the pinned compiled cache.

The [evidence bundle](evidence/lean-unified-reseed-opening-20261014/README.md)
preserves exact attempt sources, hashes, resource receipts and compiler logs,
plus final compiled objects and runner/environment snapshots. Root inspected
the final theorem premises and connections and audited the artifacts. Runtime
fingerprints remain unchanged; these changes require no SBF rebuild.
