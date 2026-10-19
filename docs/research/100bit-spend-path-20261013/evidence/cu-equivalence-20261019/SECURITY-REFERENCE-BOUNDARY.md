# Reference security boundary for CU equivalence

This scope review preserves the full equivalence objective. It separates
original theorem premises from new obligations caused by changed code. It
discharges no missing source obligation by assuming optimization equivalence.

## Soundness roots inspected

AdaptiveMembershipSoundness.membership_bound_outside is parameterized by the
protocol, relation/extractor correspondence, density, chain-read laws,
injection, terminal rejection outside the collision event, and query budget.
It explicitly keeps concrete source, decoder and collision obligations visible.

RawAdaptiveMembershipBound.membership_bound fixes the literal decoder/compiler
construction and derives the read/density/injection machinery. Its remaining
source-facing inputs include hQ, acceptance-to-formatting hformat, and terminal
rejection hterminal. Equality of an optimized implementation's decision and
ordered oracle behavior must preserve these obligations; they must not be
replaced by an assertion that valid fixtures pass.

SpendRelation and SpendAppendBinding express the spend/append checks. Local
arithmetic equivalence does not alone bind a new source caller to that relation.

## Privacy roots inspected

R1Z.PrivacyR1.privacy_R1 and R1Z.PrivacyGamesR1.privacy_R1_games retain their
honest-prover, public-base, builder, real/ideal model or real-data, and sampler
premises. The CU optimization programme changes verifier implementation, not
prover messages, challenges, masks or proof serialization. Its final transfer
must preserve the modeled public/oracle observations and settlement effects.
It does not prove privacy of timing, compute use, fee-payer linkage or network
metadata.

PrivacyOpeningCheckpoint is an axioms checkpoint importing component results;
it is explicitly not a whole source-correspondence or new privacy theorem.

## Consequences for proof work

An identical shared helper may remain universally quantified in a replacement
proof. Proving its arithmetic again is unnecessary when the equality holds for
every interpretation and both callers use the same source binding. Changed
helpers (such as the canonical dot kernel) still require their changed
contracts and invariant obligations to be proved.

For gamma-table reuse, the essential caller fact is that preparation already
computed the same power-table function at the same gamma and retained its
result. The second identical deterministic computation can then be removed
without a fresh mathematical power-table correctness proof. The actual
preparation/table/gamma dataflow and error paths must still be extracted or
otherwise bound and checked; that is the next candidate obligation.

The reference FirstCaller model already binds the actual decoder and selector
while retaining downstream tx1/observer/error and SDK/runtime boundaries.
Candidate 6 now consumes that caller and its helper/serializer theorem; see
PUBLIC-DECODE-REUSE.md. Those original boundaries remain visible. Generic
compiler/library verification must not silently become a new prerequisite,
and newly introduced interpretations must not silently become old premises.

The final combined theorem remains required: actual optimized caller models,
all replacement contracts, preserved bytes/errors/oracle order/effects, and
application of the existing security results under their original premises.
No component count or source manifest check substitutes for that theorem.
