# Exact transcript view and the row-32 decoder interface

The ordinary-record completion is now connected to the deterministic unified
run, including the first C1 message and the reseed at row 26. Adding the
actual q22 result gives the run's exact prefix before rho. A guarded decoder
returns this representation in the existing `R0C.V3.Dec` interface, and its
background law is expressed using the unified row-32 sampler.

This checkpoint closes representation and local law connections. The later
[trace-recovery connection](UNIFIED-TRACE-RECOVERY.md) also proves guarded
row-32 decoder success and trace following for the actual prover/verifier
experiment, under explicit codec, budget, and collision premises. The full
round dispatch and complete Fiat–Shamir security instance remain open.

## Deterministic run and completed records

`UnifiedRun` defines the transcript recursively from the already checked
sampler. Message zero carries C1; each later message is the indexed payload.
Its statement, length, state progression and range-map identities are proved
by induction. It does not contain a placeholder extractor or an assumed
security theorem.

`UnifiedRecords` records the actual pre-absorb, absorbed and carried states.
The first pre-absorb state is the public/C1 hash. The carried state at row 26
includes the opening-domain hash. `ordinary_challenge` identifies each
non-query challenge with the corresponding record's squeeze value and
carried state. It requires the two explicit row-zero facts: label 160 and
the five-byte empty-record encoding.

`UnifiedRecordCompletion.completed_eq_transcript` applies the older
`completeRounds` function and the new C1/payload view to those records. For
every prefix length at most 31, the result equals the unified run's literal
round list. The proof reuses the symbolic record-append and view lemmas; it
does not assume equality of the two transcript representations.

`UnifiedQueryRun` adds q22 at index 31. Its five results identify the query
challenge, the selected continuation, rho's absorb address, rho's challenge,
and the exact 32-round prefix. `JointActualView.actual_output` maps the raw
component constructed from these records and addresses to that prefix,
message 32 and challenge 32. This last theorem does not by itself show that
the backward decoder returns the constructed component.

## Recovery remains present under every background completion

The decoder's query result is optional. `JointRecoveryTotal` inverts an
actual successful context parse and obtains its endpoint seek. That seek
depends on the earlier table, not the missing-answer completion. Therefore,
for every background-answer list, recovery returns a query result at the
same query address. The result can include the q22 exhaustion/error case;
this theorem does not assert successful query selection.

`JointTranscriptView.mkPrefix` invents no query row if recovery is absent.
The preceding result rules out that branch under successful parsing.
Together with the ordinary-record count, it proves that every background
completion has exactly 32 rounds before rho when the context has 31
ordinary records.

## Guarded decoder and law

`JointUnifiedDecoder.decode` parses the context and rejects it unless the
ordinary-record count is 31. It returns the existing own/background sampler
and maps the old structured output to a prefix/message/challenge triple.
`decode_sound` exposes the successful parse and count guard.
`decoded_round` proves round number 32 for every output of every completion
returned by this decoder, including arbitrary supplied answer lists.

`JointUnifiedLaw.background_sampler_law` proves that the mapped completion
law is the outer mean over missing background answers followed by the exact
unified row-32 sampler law. It reuses `JointDecoder.output_law`, the existing
background-map theorem, and `UnifiedSampler.unified_law`. It does not assume
independence of arbitrary shared-oracle reads.

`JointUnifiedBound.decoded_bound` transfers any explicit bound for every
fixed completed prefix through a successful guarded decode. The bound and
its fixed-prefix proof remain theorem inputs. This is the density interface
needed by the existing framework, not a newly established numerical or global
soundness bound.

## Remaining integration work

The existing `JointDecoderTrace` theorem is stated over explicit semantic,
opening and query chains. Those chains and their whole-trace read premises
must be derived from the unified run, including the pre-reseed semantic end
state and the actual eight query pairs. Its recovered record list must then
be identified with `UnifiedRecords.records`. This is needed to prove actual
row-32 first-read decoding and following, rather than merely matching the
constructed output's representation.

The other decoder cases, the full dispatch, concrete classifiers and
D1/D2/D3/injection/density instance remain open. Public/payload/challenge
codecs are still abstract. Rust parsing, account authentication, settlement,
universal mask rank and the complete privacy simulator remain open. The
global oracle-query factor and collision terms are retained; no
work-normalization or grinding credit is used.

## Focused verification

Thirteen final targets passed on the capped NUC. The combined checkpoint
took 1.41 s at 3,525,256 KiB peak RSS, zero swap, and produced 30 reports
using only standard axioms or none. Every attempt used a separate 4G/6G/0
high/max/swap scope. The initial `UnifiedRecords` proof tried to normalize
the concrete row-26 transcript and reached its heartbeat limit. A symbolic
payload-value lemma replaced that reduction; the final target took 1.55 s
without increasing any limit.

Exact sources, failed attempts, final objects and resource/axiom evidence are
in [`evidence/lean-unified-decoder-20261014/`](evidence/lean-unified-decoder-20261014/).
No Rust source or runtime artifact changed, and no unchanged runtime suite
or complete historical manifest was rerun.
