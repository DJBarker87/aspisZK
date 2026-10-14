# Recovering the unified run from the actual experiment trace

The guarded row-32 decoder now recovers the exact unified transcript prefix,
message, and rho challenge from the table before rho's first read, and follows
the remaining trace to that output. The final theorem applies to the actual
prover-then-verifier experiment, so earlier adversarial hash queries are
included in the table and collision/budget hypotheses.

This is the rho case of the abstract decoder connection. Other round cases,
the combined decoder dispatch and D1/D2/D3 instance, source correspondence,
and the final numerical security and privacy claims remain open.

## Existing results reused

The proof applies `OpeningQueryTrace.recover_and_follow`, which already
combines strict ordinary-prefix recovery, the opening-domain transition,
selected query-state recovery, and joint missing-answer completion. That
family in turn reuses the older first-read ordering, duplex predecessor,
background-sampler, and trace-following results. No old theorem statement or
proof body was weakened or changed in this checkpoint.

`JointContext.parse_of_checks` binds the two final messages and their indices.
`JointUnifiedDecoder.decode_of_parse` supplies the existing 31-record guard.
`JointDecoder.follows_of_joint` and `JointTranscriptView.follows_map` preserve
the recovered output, and `JointActualView.actual_output` identifies it with
the literal unified run. Unlike the earlier forward-view theorem alone, the
new connection proves that the decoder actually returns and follows that
output.

## Deriving the old theorem's premises

`UnifiedProtocol` places the existing 33-row sampler in an `FS2.Protocol`.
Its extractor and decision procedure are explicit parameters. The unused
legacy protocol decoder field is `none`; the V3 decoder is supplied separately
by `JointUnifiedDecoder`. No theorem here asserts acceptance or extraction.

`UnifiedSteps` and `UnifiedPayloadStep` derive the state transitions with
symbolic prefixes. Row zero includes its public/C1 initialization hash; row
26 includes the opening-domain hash. The semantic phase's last pre-reseed
state is kept separately from the carried post-reseed state. `UnifiedPhases`
and `UnifiedPhaseRecords` prove that the old two-segment record representation
is exactly the first 31 records of the unified run.

`UnifiedChainReads`, `UnifiedQueryReads`, and `UnifiedTraceReads` derive all
required reads from the verifier: initialization, ordinary absorb/squeeze/
advance cells, reseeding, all eight query pairs, and rho. They use the existing
`FS2.verifier_reads` and `FS.eval_consistent` theorems. No individual hash-read
or phase-transition assumption remains in the final recovery theorem.

`UnifiedPrefixedReads` permits a prior consistent trace. The final
`UnifiedExperimentInjection.decodes_and_follows` takes an arbitrary prover
program and derives that consistency from `FS.eval_consistent`; the old
`FS.experiment_eval` identifies the combined trace. Consequently the decoder's
table includes the prover's queries, rather than starting at verifier entry.

## Exact retained premises and limits

The final theorem retains the existing abstract `Params` codec/duplex
interface, `5 <= p.D`, public initializer fit, public byte length below
`2^32`, row-zero label 160, and the empty-record encoding for payload zero.
Its first-read budget and both collision exclusions are stated on the complete
experiment trace. The exclusions are the existing duplex collision event
and the trailing-state parser collision event. The proof does not assume
successful parsing or a recovered transcript as an input.

This supplies one deterministic injection case. It does not establish all
of `Inj3`, choose the concrete acceptance classifier/extractor, or supply the
fixed-prefix numerical bound required by the existing local sampler law.
The old generic Fiat–Shamir reduction still has its explicit query factor
and collision term; this checkpoint makes no absolute 100-bit claim and
adds no grinding or work-normalization credit.

The new statements describe the Lean sampler/verifier model. Rust byte
construction, account/settlement enforcement, and the universal masking and
simulator arguments remain separate obligations. Runtime sources and the
14 central runtime fingerprints are unchanged; no SBF or runtime regression
is justified by these Lean-only additions.

## Focused verification

The fifteen new modules, including the final combined import/axioms target,
are verified on the pinned NUC workspace. Each attempt has an exact source
snapshot, hash, exit status, wall time, peak RSS, and swap count. All jobs use
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, with Lean's 5000 MB limit.
Failed and superseded green attempts are preserved. The final combined
checkpoint passed on its first attempt in 1.46 s at 3,528,556 KiB peak RSS,
with zero swap. Its 46 axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. It was run once after the focused
dependent targets passed.

See `evidence/lean-unified-trace-recovery-20261014/` for the sealed manifest,
compiled-object archive, all attempt logs, and root validation. This is a
focused component replay using the pinned cache, not a replay of every
historical proof or a full protocol security certificate.
