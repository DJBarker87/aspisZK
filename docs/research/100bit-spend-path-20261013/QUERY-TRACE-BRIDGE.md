# Following query completion on the actual trace

The local q22-to-following-round decoder now has both a checked
trace-following theorem and an adaptive-continuation probability bound.
This extends the independent-answer [completion law](QUERY-COMPLETION-LAW.md).
It is not the full R1 Fiat–Shamir or source theorem.

## Trace and decoder

`QueryNextTrace.follows_after_query` derives the premises of the existing
`bfollow_ok` theorem from the whole trace and the existing duplex collision
complement. It does not assume the desired trace-following result, address
distinctness, missing-cell freshness, or unused query tail in the earlier
table.

The explicit inputs are a consistent whole trace, its first-read count
bound and collision complement, the eight query advance equations and
eight squeeze/advance read facts, the query absorb read and parsed frame,
and the following parsed absorb with the selected query state as its
leading bytes. The following round's squeeze and advance must also occur
in the whole trace. The theorem proves that the local completing sampler,
started at the table before the following absorb's first read, returns
exactly the actual query result and following challenge.

The proof derives the selected predecessor path from the earlier table.
Its missing squeeze cells are fresh in that table and occur in the suffix.
Their order relative to the new squeeze is unrestricted. Their states
differ from the new absorb's output by the old no-collision theorem;
encoding separation excludes overlap with the absorb and advance addresses.
The new absorb precedes its own squeeze and advance by the old prefix-read
lemma. These facts discharge the no-duplicate, freshness and order conditions
of `bfollow_ok` rather than adding them as premises to the final theorem.

`QueryNextDecoder.decode` is an actual local decoder function of the queried
address and preceding table. It parses the predecessor state from that
address and searches the table for the query absorb boundary. It does not
receive the actual oracle result or a guessed stopping index.
`decodes_after_query` proves decoder success and exact trace following for
the concrete following absorb frame. The round index is supplied as a
parameter; identifying this with R1's row 32 remains an instance duty.

## Local adaptive bound

`QueryNextBound.continuation_bound` reuses the existing `chainB` theorem.
For an arbitrary adaptive continuation program and a fixed starting table,
endpoint and absorb address, the mass of following this sampler to a bad
output is bounded by any bound valid for every fixed background completion.
This moves beyond an independent-answer calculation. It is a bound for the
local event; a union over adversarial first-read entry points has not been
instantiated for the complete R1 protocol.

`QueryRhoBound` supplies that fixed-completion bound for the existing
21-root rho exception. It explicitly requires the challenge projection to
equal the encoded modulo sampler, including its input/output equivalences.
Residual data and the 22-query list are functions of the recovered background
component; they cannot depend on the fresh rho or advance answer through
these function arguments. The local adaptive event is bounded by the
existing `rhoCap`, which is strictly below `2^-119`.

`QueryRhoAcceptance` uses the existing accepted-query implication to bound
the event that a query misses the matching support but the field-level
query checks accept. It is therefore an acceptance-error corollary, not
only an unrelated polynomial-root count. The sampler identity and the
connection of the fixed residual data to actual authenticated source words
are still explicit integration obligations.

## What this does not close

The new local decoder returns the recovered query component, not all earlier
R1 records. The complete `Inj3`/`ChainDensity3` instance still needs earlier
messages, the public/C1 initialization and opening-domain hash edges,
canonical parsing, a full prefix constructor, and the actual D1/D2/D3
connections. The generic `theorem43` retains its `Qtot * maxErr + collision`
form; no query-work credit or removed `Qtot` factor is claimed here.

This step does not change the larger q22 envelope in the ledger, establish
source/account/settlement refinement, or close the privacy theorem. The
less-than-`2^-119` statement is for the local final batching event under the
listed premises, not a 119-bit claim for the entire spend.

## Verification

Ten final focused NUC targets passed. `R1QueryTraceCheckpoint-a` ran in
1.36 seconds at 3,525,648 KiB peak RSS, zero swap, under the 4G/6G/0
high/max/swap cgroup caps. Its 18 axiom reports use only `propext`,
`Classical.choice` and/or `Quot.sound`.

Source base: `84de41db1c7a26101183efa8bd4fe2b06a31bb40`.
Checkpoint source hash:
`e7ff92dc22e051917b1d89a49a7dbc751b02faf63a770247a05cafb95506d184`.
The [evidence bundle](evidence/lean-query-trace-20261014/README.md) records
all attempt sources, including failed attempts, exact receipts and resource
logs, the pinned runner/environment, and final compiled objects.

No historical theorem or Rust source changed, so no unchanged runtime or
package-wide formal regression was rerun.
