# Checkpoint ABI draft

Base: 73772c55b, codex/cx-ckpt-abi-draft-20261021. No merge or push.

## Stage 1: source inspection

The physical source is `crates/aspis-r1-cost-probe/src/verifier.rs:326–435`.
`checkpoint` writes the fields in C5 order. `resume` checks length/header,
then proof hash, public hash and checksum with short circuit, before decoding.
It rejects repeated queries. The saved-ten domain has header next=10; the
source accepts other next values up to 22, so this is not a whole-resume
all-input specialization.

`OraclePortCheckpointOracleC5.resumer` always issues all three digest calls;
it cannot be used as a total source refinement on rejection paths.
`OraclePortCheckpointPreparedC5.decode` allows duplicate queries; its roundtrip
alone is not a source resume theorem. `R9PoolCheckpointCodec` explicitly uses
an unrelated logical encoding, not the physical ABI. Existing extracted
`resume_three_inputs`/`successful_resume_calls` expose source digest witnesses,
not writer/decoder equality. R22's retained remaining-summary explicitly leaves
the full owned-Vec loop, allocation/iterator joins and cursor sequencing open.

`OraclePortFrozenOrder.dV_frozen` contains admission, parsing, queries,
six slots and arithmetic, with no checkpoint stage. The checkpoint joins at
the surrounding verifier driver. No concrete frozen caller/tree identity is
available here to instantiate `ConeJoin .checkpointAbi`.

Planned additive work: a source-shaped reference for the saved-ten ABI with
short-circuit digest failures and query uniqueness; total model codec facts,
accepted save/resume state and exact ordered reads; explicit source witness
boundary. This is not an assertion that the extracted codec is identified.

## Stage 2: total saved-ten reference and exact read order

`OraclePortCkptAbiCodec.decode_encode` computes the exact Option result on
every typed encoded saved-ten input: complete decoded fields for injective
queries and `none` otherwise. `repeated_query_rejected` makes the previously
missing uniqueness restriction explicit. `save_contract` includes prepared
fields, the computed ten-step accumulator and all three digest bindings.

`OraclePortCkptAbiReference.resume_eval` is an all-input ordered evaluation
formula with zero/one/two/three-read rejection paths. `resume_saved` is total
on all authentic saves, including query-uniqueness failure.
`accepted_saved_fields` identifies the entire prepared value and accumulator
and the twelve-step resumed state. `writeResume_trace` proves the exact six
address/answer pairs, including repeated proof/public/body bytes.
These are reference facts, not equations for the frozen Rust writer.

`OraclePortCkptAbiRejection.c5_eager_log_mismatch` proves that the earlier C5
resumer cannot be a total ordered-log source refinement after proof-hash
failure. The source-shaped reference fixes this error timing. Its header is
explicitly restricted to S2 saved.next=10; arbitrary source resume inputs
with other next values are outside that specialization.

## Stage 3: extracted source outputs and immutable reader bytes

`OraclePortCkptAbiReader.raw_total_exact` strengthens the existing raw-body
contract to exact returned bytes plus cursor and backing-slice equality.
`OraclePortCkptAbiReadSequence.readMany_total` composes this structurally.
`savedTen_reads_total` covers every raw field width, including all 22 u32
queries and all 64 weights: offset 80 + 1656 = 1736. No concrete byte vector
or large field recurrence is reduced. The required unwrap-on-Ok is explicit.

`OraclePortCkptAbiSource.successful_entry` inverts the actual emitted resume
prefix, without comparison soundness, exposing the first three raw calls.
`entry_exact` identifies their exact state/root slices under the atomic raw
adoption law. `OraclePortCkptAbiSourceFields.successful_fields` inverts the
complete emitted body: every output Prepared/Accumulator field, all query
reads, validation, semantic-alpha input, allocation, weights input, final
cursor and next-byte cast have explicit source-call witnesses. This theorem
needs only successful resume, not decoder/field/arithmetic correctness.
`OraclePortCkptAbiSourceBacking.all_fields_same_backing` proves the same
checkpoint across all 16 field cursor boundaries under atomic raw/readE/readK
preservation contracts. It does not assume a whole-resume equality.

The complete output inversion is generated as a bounded sequence of Result
cases. Each success branch weak-head-reduces only its outer continuation;
there is no broad field-codec/recurrence unfolding. Failed local elaborations
and missing-cache path attempts are retained. No cap or theorem limit was
raised, no unchanged source/environment attempt was repeated, and no failed
axiom report is accepted as current proof evidence.

## Boundary that stops complete-cone promotion

The complete accepted frozen TX1/TX2 refinement requested by the lead is
**not proved**. Four concrete missing joins remain:

1. The source `checkpoint` writer and concrete field codecs/cursor/Vec
   operations are not instantiated against the reference. Existing R22
   Kani contracts establish safety/canonicality, not exact raw-byte values.
2. The available raw-body theorem explicitly abstracts the emitted unwrap
   whose debug instance mentions a nonstandard Formatter axiom. Importing
   that concrete instance would violate this job's standard-axioms rule.
3. The reached source Prepared/context, unique queries and ten-step state
   have not been identified with the reference model's data/context.
4. `dV_frozen` has no checkpoint operation inside its decision. The missing
   surrounding driver/caller identity and checkpoint-site instantiation
   cannot be inferred from a model codec roundtrip or from source witnesses.

Thus no concrete `ConeJoin .checkpointAbi`, `PerConeJoins` inhabitant,
`AcceptedRunJoin`, or new endpoint is claimed. The cone audit row stays (d)
for the whole cone and now lists the proved local/source fragments.
R19 and the frozen headline are preserved byte-for-byte; signature diffs
record zero premise removals. The work remains an unmerged draft.

## Focused evidence freeze

Ten new `OraclePortCkptAbi` modules contain 33 theorem declarations; 43 final
axiom reports (including the import audit) use only subsets of
`{propext, Classical.choice, Quot.sound}`. The 25 focused attempts comprise
11 successes and 14 corrected local/cache failures. All receipts include
exact command, source revision/hash, direct-import/environment fingerprint,
exit, wall, RSS, swaps, complete axiom reports and errors. Maximum measured
RSS across all attempts: 3,625,566,208 bytes; swaps: zero throughout.

Final target `OraclePortCkptAbiFreeze`, attempt 2: exit 0, wall
17.493518167175353 seconds, peak RSS 3,555,311,616 bytes, zero swaps, source
revision `31442b7cb5584c76b438f1a778037acce7d0fb83`; all ten axiom reports
standard. Attempt 1 exposed an import-path selection of a missing historical
R0C object; attempt 2 corrects cache-path precedence. No dependency rebuild,
shared-object overwrite or unchanged-source/environment rerun was used.

`audit-result.json` records the passing source/object/receipt/theorem/scope
and signature-preservation audit. This is a focused mixed-cache import
check, not a coherent frozen release replay. The full release manifest is
not run while the concrete endpoint/source join remains incomplete.

No existing Lean module, S-candidate, M10 file, production Rust, key or
shipped artifact changed. Commits are local; nothing was pushed or merged.
