# Initial and final decoder cases, and recovery of early prefixes

The initial decoder and rho decoder now return the exact `FS2.Protocol`
transcript/message/challenge at their first queried addresses on the actual
prover-then-verifier experiment. The initial decoder also has its completing
sampler law. A separate theorem combines the two recovery collision events
on that experiment into the existing `3 * Qtot^2 / 2^256` budget.

Before each row from 1 through 26, the typed semantic-prefix decoder recovers
C1 and the exact earlier unified records from the table before that row's
absorb. This is prefix recovery; those rows still need their completing
samplers and decoder dispatch. At row 26 the recovered prefix ends at row 25,
so this theorem does not incorrectly replace the row-26 reseed by an ordinary
advance.

## Exact reuse and checked connections

`UnifiedFramework.readsChains` supplies the existing `FS2.ReadsChains`
interface for the chain-running verifier. `initial_firstCell` and
`rho_firstCell` identify the first queried addresses of rows 0 and 32.
`UnifiedRhoCase` restates the preceding trace-recovery result at an arbitrary
address satisfying the protocol's first-cell equality and returns the actual
protocol projections, rather than only the separate `UnifiedRun` projections.

`UnifiedInitialDecoder` wraps the existing `InitialDecoder` in the shared
prefix/message/challenge output type. It preserves the strict public-byte/C1
parser and its own completing sampler. Successful decoding implies that
every returned output has round number zero. `UnifiedInitialLaw.sampler_law`
reuses `InitialSamplerLaw.own_law` and `DuplexSamplers.initial_law`; its
`decoded_bound` still takes the fixed-prefix bound as an explicit premise.

`UnifiedInitialCase.decodes_and_follows` derives all four initialization
reads and trace consistency, reuses `InitialDecoder.decodes_initializer`,
and maps its output to the protocol triple. It includes earlier prover
queries. It needs public length below `2^32`, initializer fit and `5 <= p.D`,
the first-read budget, and the existing duplex collision exclusion. It does
not need the dummy payload-zero encoding/label premise or the extra parsed-
tail collision exclusion needed by recovery of the later prefix.

`UnifiedSemanticRecovery.typed_before_row` uses the previous-state function,
the checked state-step/read lemmas, `InitialWalkTrace.walk_before_next`,
and `RawRoundCompletion.decode_records`. It derives parser success for all
`0 < n <= 26`, with fuel 27. `UnifiedSemanticRecords.records_eq` converts
the list representation by symbolic pointwise equalities. No concrete
recurrence is normalized. This result retains the row-zero codec premises,
prior-trace consistency, query budget and duplex collision exclusion.

## Collision event on the same experiment

`UnifiedCollision.Coll` is exactly the union of the old duplex event and
the trailing-state parser event used by reseed recovery. `outside` supplies
the two exclusions. `mass` applies `FS2.Duplex.coll_mass` and
`ParsedStateCollision.mass` to the same prover, verifier and statement,
then sums their bounds. It proves the `3 * Qtot^2 / 2^256` charge under an
all-oracle distinct-first-read budget. It assumes neither independence
between these events nor successful decoding.

## Remaining full-protocol work

The two endpoint cases are not a combined `Inj3` instance. The address-only
dispatch must cover the intervening ordinary, reseed and query cases and
must choose the correct case without relying on an oracle-dependent round
input. The early-prefix theorem supplies one part of that work. The complete
D1/D2/D3 instance, concrete sampler density/extraction composition, Rust and
account correspondence, and universal masking/simulator argument remain open.

The numerical inventory still gives exact q22 ratio
`choose(9557,22)/choose(262144,22)` (about 105.142 bits). The conservative old
`1+delta0` envelope yields about 105.136 bits, consistent with the current
arithmetic ledger. The generic theorem charges `Qtot * maxErr` plus collisions;
these additions neither remove that factor nor instantiate a numerical R1
security theorem. No grinding or work-normalization credit is included.

## Evidence

Ten focused NUC targets, including one combined checkpoint, are recorded in
`evidence/lean-unified-endpoints-20261014/`. Every attempt has an exact source
snapshot, hash, exit status, wall time, peak RSS and swap count. All jobs use
4G/6G/0-swap cgroup limits and Lean's 5000 MB limit, reusing the pinned cache.
The final import/axiom target passed on its first attempt in 1.49 s, with
3,528,604 KiB peak RSS and zero swap. Its 20 audits contain only `propext`,
`Classical.choice`, and `Quot.sound`; it was run once after the dependent
targets passed.
The root audit checks current final sources, receipts, compiled-object archive,
and unchanged runtime fingerprints. No runtime or SBF rebuild is needed for
these Lean-only additions.
