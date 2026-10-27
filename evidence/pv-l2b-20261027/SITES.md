# Candidate source obligations, not an endpoint discharge

Revision c57a344726745387efb38d1571d885c69ce829ee. L3's historical line
numbers have moved; the function names and current locations below control.
N1 and N7 are intentionally not worked. No counterexample on honest valid
inputs has been checked. No absence-of-leakage claim is made.

| Site | Candidate location | Exact invariant / remaining association |
|---|---|---|
| V354 m31 | state_only_hiding.rs:419–433 | IID masked 31-bit candidates under the E2 ROM/expander association; public number/order of requested cells. 16-draw cap, one rejected value P. |
| V354 next_word | state_only_hiding.rs:409–417 | word in 0..8, initial word=8; refills at public position within the simulated consumed-word history. Counter wraps as u64. Full hash-call observation law still required. |
| V354 qm31 | state_only_hiding.rs:435–440 | Four left-to-right capped scalar calls, stopping at first exhausted limb; preserve failed prefix, not just successful four-limb outputs. |
| V352 entropy | state_only_entropy.rs:211–242 | Public nonce guard is directly simulatable (zero nonce exits without an OS draw); otherwise IID independent 64-byte OS fills under E1, including status/partial-fill/failure schedule. Zero predicate scans all 32 bytes. First-zero short-circuits the second predicate. OS failure independence remains P under option B. |
| N2 padding | state_only_hiding.rs:289–309 | 1024-row shape, active padding cells zero; inactive padding sum zero. Generated padding and balance must be associated with actual produced buffers. Public active mask controls the first conjunct. |
| N3 canonical | host_semantic.rs:144–175 | Every 26×1024 base cell is <P; D/G's four limbs are canonical and byte round-trip parser accepts. Compiler output and every applied-mask arithmetic result must preserve this domain. Successful guard checks alone do not prove it on honest input. |
| N4 balance | prover.rs:200–208 | 16 noised compiler C1 columns and 10 mask-only columns have inactive sum zero; D/G/H1 padding too. The caller rebalances the whole noised C1 column after applying masks; no zero-sum premise on the original compiler C1 column is required. Audit and rebalance must use the same inactive-row set and canonical field operations. |
| N5 helper | host_semantic.rs:74–76; prover.rs:214–215 | Helper length 1024 and copy producer/consumer multiset equality imply total helper sum zero outside inverse failure; padding preserves that sum. The later prover check sees the same column 26. |
| N6 boundary | host_sumcheck.rs:105–107 | Native oracle equals the semantic low-degree oracle, initial claim is its Boolean-cube sum; interpolation equals the degree≤27 round polynomial; subsequent running claim is its challenge evaluation. |
| N6 terminal | host_sumcheck.rs:68–70 | After 10 substitutions, native oracle evaluation equals the running polynomial evaluation; no native evaluation error on honest input. |

For N5 the pre-helper ActivePole return belongs to existing `poleBad` **only
under the existing P ∧ not-V predicate at the same attempt and same coupling**.
This task does not reclassify a failed N2/N3/N4/N6 guard as poleBad, nor introduce
a new uncharged event. The sum guards need honest invariants in addition to
pole-freedom. Existing source-boundary proofs in
`ProverCommitSemanticGuards55.{initial,chain,no_rejection}` retain polynomial,
canonical-running and oracle/model premises; their names do not discharge the
candidate's complete caller association.

## Simulator samplers

Scalar: q=1/(P+1)=2^-31. Draw independent Bernoulli(q) rejection flags, at most
16 per limb. Return exhaustion if all reject (mass q^16=2^-496). Otherwise the
number r of rejects has mass q^r(1-q), 0≤r<16. Independently sample the accepted
value uniformly in [0,P). Each specified accepted value at r has mass
q^r/(P+1), equal to q^r(1-q)/P. Four scalar samplers run left-to-right for QM31;
stop on the first failure. Maintain the cumulative consumed-word count n:
read offset 4(n mod 8), logical block index floor(n/8), hash counter modulo 2^64; refill before a read when the
source word cursor is 8. Do not resample or hide failed limb prefixes.

Entropy: first test the public nonce; if it is zero, reproduce the immediate error and make no OS draw. Otherwise B=2^256 and z=1/B. Per successful OS fill, first-zero rejection has
mass z; first-nonzero/second-zero rejection has mass (1-z)z; acceptance mass
(1-z)^2. Thus q=2z-z². Draw the capped geometric rejection count (cap 16), and
for each rejected draw sample its class with probabilities z/q and (1-z)z/q.
First class evaluates one predicate, second class evaluates two; success also
evaluates two. Sample the accepted pair independently and uniformly from the
(B−1)^2 nonzero pairs. Entropy error/partial-fill schedules require their
existing E1 joint kernel law, not an invented always-success OS sampler.

These are **ideal IID-coordinate samplers**. Their algebraic laws do not
identify deterministic SHA with independent words. E1/E2 associations, ROM
query freshness/collision handling, public requested-cell geometry, complete
failed-prefix transport and native owner composition remain obligations.

## Public geometry association found by source inspection

`state_only_hiding.rs:159` obtains the public row list and sets its Boolean
entries. `pair_forest_hiding.rs:190` packs the same row-list generator into
u16 masks. The prover obtains those masks at prover.rs:196; source D expands
those masks back to Boolean entries at state_only_entropy.rs:758. This is a
structural source association, not a machine-checked bit-packing/fold theorem.

All sixteen C1 columns are rebalanced after mask addition:
apply_mask_material_for_layout → balance_mask_columns →
balance_mask_column → balance_m31_copy_inactive. The final dependent cell is
set to the negative sum of all other inactive entries. There is no need to
assume a zero inactive sum before this operation. The initial report draft's
stronger requirement was corrected after inspecting this actual call chain.

## Checked literal scalar projection

`PV_L2B_SourceWords.source_scan` projects a literal UInt32 AND/compare scalar
control translation to the generic scan; `source_count_relabel` transports
its consumption count under an explicit accepted-value relabeling. The
provided raw-word prefix must cover the requested fuel (16 in the caller).
These are source-helper results; the actual expander stream's E2 law, cursor
state refinement and native effects remain named obligations. `blockIndex`
is a logical Nat block ordinal. The Rust counter is u64 wrapping; its hash
counter is this ordinal modulo 2^64. E2 must preserve the existing finite
read bound/no-address-repeat argument, rather than assume an infinite fresh
word stream past counter wrap.
