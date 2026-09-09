# Private C1 recovery, independent of final distance

Research base: `113dc5dacbf630c234cc6498385913507c171f8f`, on
`research/v8-no-work-100-20260907`. Borrowed formal closure remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, Lean 4.32.0, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. This is a continuation of
[the selected component result](selected-component-continuation.md), not a
new profile, code-rate sweep or production claim.

Main was inspected at `544e366ddcde2646a6799edf95e6879cd459984d`.
Its concurrent `V7Tag73RootQueryBatchForkBridge.lean` edit and untracked
`results/v7-all-reachable-cu-bound-testnet-20260907/` were left untouched;
the imported closure's recorded hashes still pass the final read-only audit.

## New connected result

`EarlyC1SampleGame.accepted_coefficient_failure_bound` is kernel-checked.
For a fixed received C1 whose **existing mathematical** `earlyC1` object is
`some p`, it bounds joint acceptance and failure to recover the sixteen
semantic message columns using a fresh uniform private 513-fibre sample.
It requires **no assumption on C2 or final-polynomial distance**. The code,
coordinates and inverse-matrix interfaces are explicit; canonical M31
descent, authenticated access and actual Rust extraction are not silently
inferred from a QM31 mathematical received word.

The new exact bound is

```
choose(16535,104) * choose(262144-104,513-104)
------------------------------------------------
choose(262144,513) * choose(129,104)
```

Its display value is about **2^-134.4530038986**; exact integer/rational
arithmetic verifies it is below `2^-134`. The symbolic counting inequality
and its decoder composition are Lean-proved. The large numerical comparison
is an arithmetic check, not a new giant kernel-reduction certificate.

This is a coefficient-decoder error bound, **not a payment-witness or global
V8 soundness bound**. The earlier 137.7548-bit hypergeometric arithmetic is
not replaced or replayed: the new factorial-moment upper bound is slightly
weaker but has a checked universal counting proof connected to this decoder.

### What is actually connected

1. `EarlyC1GaoRecovery.badFibres_card` unfolds the existing optional object's
   successful return theorem. It derives its own common support and hence
   at most 16,535 bad C1 fibres; this is not an extra `candidateMember`
   premise. The candidate still need not exist at every C1 commitment.
2. The decoder receives only the fixed received word, public algebraic data
   and the private sample. **It does not receive p**, an honest witness,
   expected message coefficients or an anchor pointer.
3. The sample's literal four-slot embedding yields 2,052 distinct source
   indices. All sixteen columns use the **same** sample and bad-fibre set.
   Existing finite-fuel Gao completeness shows at most128 bad sampled
   fibres suffice: at most512 scalar errors are within the ambient
   degree-at-most1024 polynomial's 513-error decoding radius.
4. `failure_requires_129` therefore forces at least129 bad sampled fibres
   for any coefficient failure. It does not assume decoder success.
5. `EarlyC1SampleGame` sorts each 513-subset with `orderEmbOfFin`, proves its
   image is exactly that subset, and applies the same concrete decoder.
   This closes the ordered-sample versus unordered-probability interface.
6. `PrivateSampleMoment` double-counts 104-subsets of the fixed bad support.
   Each failing sample contains at least `choose(129,104)` such witnesses;
   each fixed witness occurs in at most `choose(T-104,513-104)` samples.
   This gives the displayed joint bound without a sixteen-column union.

`accept(S)` is arbitrary in the final theorem. It may include all later
proof choices or restrict to far-final executions. The proof bounds the
**intersection** of acceptance and decoder failure under the original
private sampling law; it does not condition on acceptance and claim the
remaining samples are uniform. The received word and bad support must be
fixed before this private sample.

## Actual missing interfaces and access contract

`AlgebraInterfaces` visibly retains the following public obligations:
the actual natural-circle evaluator equals the selected original encoder;
sample points lie on the circle with distinct Laurent parameters; the
chosen target points lie on the circle; the supplied public coefficient
matrix is a left inverse of the evaluation matrix; and the explicit tower
constants satisfy their identities. None is an assumed decoder-success or
payment-validity predicate. Instantiating all of them from current source,
and refining the actual Rust Gao implementation, remains necessary.

| Access stage | What this continuation establishes |
|---|---|
| Fixed full-oracle C1 model | One connected mathematical coefficient decoder and private-sample failure bound |
| Authenticated sampled openings | Literal requested indices/counts are identified; root-bound raw-word coupling and canonicality must be supplied by the existing authentication work |
| Actual replay/rewinding extractor | No new guarantee of obtaining those requested openings, finite retries, query-log coverage or running time |
| Checked payment witness | Requires semantic/copy/ownership/path/public-context constraints and the literal validator endpoint after coefficient recovery |

The private sample is **513 fibres, not q513 verifier queries**. It reads
32,832 semantic field values at 2,052 points per column. At four bytes per
M31 value those semantic values occupy 131,328 bytes if materialised. Full
authenticated C1 leaves also include ten non-semantic lanes and salts:
using the existing 403-byte C1 leaf plus32-byte salt, an optional separate
513-leaf multiproof has a maximum4615-node binary frontier, giving343,145
bytes without IDs or345,197 bytes with explicit u32 IDs. These are
**extractor access cost models**, not transmitted V8 proof sections or a new
implemented opening oracle. The q22 transcript count floor is24 by leaf
count alone; this neither guarantees the required sample nor a working
replay schedule. No extractor runtime or peak-RSS measurement was made.

The theorem's sampler is a fresh ideal uniform subset. It does not refine
the executable fixed-SHA test coins or charge a finite sampler's exhaustion.
The old4096-draw exhaustion arithmetic is not automatically a proved sampler
implementation. No honest search, nonce selection or work contributes bits.

## Correct remaining accepted-extraction event

The target is still `Pr[A ∧ ¬X]`, where X returns a checked valid payment
witness within declared resources. The following is an obligation map, not
a claimed complete actual-verifier partition.

| Precedence/class after the corresponding source coupling | Status |
|---|---|
| Missing authentication/word interpretation, queried-pole/source mismatch, replay abort/fuel/missing response/challenge mismatch, unavailable private openings | Remain explicit; no invented numerical probability |
| `earlyC1=some p`, this private decoder does not return p's semantic projection | New bound applies in **both near and far final** regimes, under the stated interfaces/law |
| Correct coefficient recovery, but no checked payment witness | Still need acceptance-to-selected semantic/copy constraints and literal validator completeness |
| Far final and wrong ordinary/OOD claims, even if `earlyC1=some p` | Coefficient recovery does not bind these claims; their accepted bad-payment contribution remains unresolved |
| `earlyC1=none` | Existing near-final sparse-Good result remains available on its own event; remaining accepted extraction failures are not dropped |
| Any execution returning a checked valid witness | Zero contribution to failure, regardless of distance or which witness was returned |

In particular, `earlyC1` constrains all26 C1 lanes while the witness decoder
reads only16 semantic lanes. Failure of this particular optional object is
not synonymous with absent recoverable semantics. Nor is recovery of a
QM31-valued tuple yet recovery of a canonical base-field payment trace.

For a pipeline that validates recovered semantic coefficients, exact recovery
of an independently valid tuple would imply successful extraction. This
continuation **does not assume that tuple valid to manufacture a completed
payment theorem**. The missing acceptance-to-validity implication, including
far executions with incorrect point claims, remains a central task.

### Ledger discipline

The new error event uses only private extractor randomness. It contains no
relation-repair term. The earlier near-final gamma/image/row results already
charge their four degree-six repairs once and remain unchanged. There is no
automatic sum of the new134-bit ceiling with the earlier117-bit or105-bit
ceilings: full event precedence, source coupling and the unbounded terms
must be justified first. Global accepted-extraction error and remaining
global error allowance remain null in the machine-readable evidence.

The actual Fiat–Shamir lift still needs oracle prequeries, nonce/retry
selection, forks/restorations and extractor time/memory/calls. The ideal
private-sampling theorem is not security against unlimited offline search,
and gives no quantum claim.

## Tests, regressions and costs

`private_sample_checks.py` checks the new double-count identities and
inequality on2,870 exact small cases, including958 equality cases, and
independently evaluates the selected bound in two algebraically different
forms. An explicit timing falsifier chooses bad=S **after** sampling in an
eight-position model: its failure probability is1, while falsely treating
that support as fixed would give1/2. These are finite checks, not a
cryptographic Monte Carlo estimate.

Existing regressions are preserved without unchanged heavy reruns:
original/paired root products and invalid far component claims remain
charged; high-J own-support recovery is not same-support recovery;
T512 and the zero-fold image kernel still require the carried image gate;
shifted kappa/rho and later collisions remain; harmless D corruption beyond
the radius is not extraction failure. The previously recorded V7
`inactiveExact` assurance item is unchanged.

There are no verifier, transcript, mask, protocol-default or production
changes. The body remains

```
697*16 +52 +24 +22*621 +2*296*26 =40,282 bytes.
```

No new CU, prover-time, real-extractor-time or full-view-ZK claim follows.
No new public messages or witness-bearing artifacts were produced. Existing
optimization measurements and the unapproved q23/quintic controls are not
reclassified by this mathematical work.

## Source interfaces completed alongside recovery

[SelectedSparseMle](selected-sparse-mle-review.md) proves the actual modeled
reverse Boolean-suffix scan, shift/OR index construction, length check and
weighted table read. The source-shaped optimized successor sends1014 to1015.
The positive-transfer last pack receives those reads from the **same
arbitrary amount/inverse tables**; its zero value is equivalent to
`amount[1014]*amount[1015]*inverse[1014]=1`. It assumes neither an honest table
nor decoder success. This closes the previously missing sparse-lookup
interface, not acceptance enforcing the Boolean residual or a complete
Rust-machine translation.

[QueriedInverse and QueriedResidual](queried-pole-review.md) connect the
field-level checked nested-norm inversion to the selected quotient/fold
residual. The proof derives reciprocal correctness from the returned checked
buffers, including both the `4*i+j` QM31 entries and the `2*i,2*i+1` base-field
entries; it does not supply reciprocal correctness as a new hypothesis.
The actual stored slot order, affine interpolant numerator and fused fold
yield **final minus folded received value**, matching the carried shifted
query batch. A queried member of the existing pole-fibre set deterministically
returns failure in this model, connecting totalized division to its checked
query boundary.

The optimized line-norm algebra is checked, but the concrete mutable
norm-buffer/Vec construction, packed gamma decoding, parser, authentication
and actual byte-execution refinement are still separate. This is not a
claim that the full source-to-game correspondence is finished or that a
zero denominator is a new negligible-probability event.

## Focused evidence and reproduction

[Machine-readable evidence](private-c1-recovery-evidence.json) records current
source/olean hashes, log hashes, exact rational values and every axiom audit.
All six changed leaves passed with only `propext`, `Classical.choice` and
`Quot.sound`, no new axioms or retained `sorry`, and zero swaps. Existing
dependencies were reused; no full formal suite, Rust/SBF gate or unchanged
heavy replay ran. The separate agents' reports identify each source boundary.

| Changed leaf | Final log | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|
| PrivateSampleMoment | [v2](experiments/private-sample-moment-v2.log) | 0 | 2.00 | 2,876,899,328 | 0 |
| EarlyC1GaoRecovery | [v2](experiments/early-c1-gao-v2.log) | 0 | 11.44 | 5,737,594,880 | 0 |
| EarlyC1SampleGame | [v2](experiments/early-c1-sample-game-v2.log) | 0 | 8.52 | 5,720,260,608 | 0 |
| SelectedSparseMle | [v2](experiments/selected-sparse-mle-v2.log) | 0 | 12.39 | 5,655,740,416 | 0 |
| QueriedInverse | [v2](experiments/queried-inverse-v2.log) | 0 | 14.00 | 5,607,866,368 | 0 |
| QueriedResidual | [v2](experiments/queried-residual-v2.log) | 0 | 20.76 | 5,739,167,744 | 0 |

These times/RSS values measure proof checking, not proving or extraction.
The6 first preflights' local syntax, coercion, namespace and rewrite errors
are retained as failed logs, not included in proved evidence. In particular,
the concrete choose-expression mismatch was fixed by rewriting the domain
cardinality **on both sides**; the natural-polynomial conversion used a named
evaluation lemma instead of unfolding the giant expression. No memory cap
increase or large concrete-field enumeration was needed.

The auditors verify all recorded source/cache hashes against current files.
Runners differ in pre/post coverage, which is recorded per leaf rather than
claiming they all emit the same marker. The generic private-moment run
predates adding the Gao cache path to its runner for the dependent leaf;
both runner hashes are retained. Its loaded imports are unchanged and
verified. The source closure borrowed from main is still pinned to26a9,
not silently updated to main's concurrent commits.

From the research worktree, using **unused** log paths and serial jobs:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_residual_extraction.sh PrivateSampleMoment /tmp/private-moment-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_gao.sh /tmp/early-gao-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_residual_extraction.sh EarlyC1SampleGame /tmp/early-sample-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_sparse_mle.sh /tmp/sparse-mle-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_queried_boundary.sh QueriedInverse /tmp/query-inverse-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_queried_boundary.sh QueriedResidual /tmp/query-residual-recheck.log
python3 docs/research/v8-no-work-100-20260907/experiments/audit_private_c1_recovery.py --check-recorded
```

The new exact small checks are `private_sample_checks.py` and
`early_c1_projection_control.py`. The latter's49 constant-code tuples retain
the semantic16-versus-all26 classifier obstruction; it is not a source
payment-proof experiment. No witness or owner secret appears in the outputs.

## Decision

The residual problem is smaller in a useful sense: far helper/final noise
does not by itself defeat this C1 coefficient extractor when the fixed early
C1 candidate exists. The still decisive soundness step is to tie accepted
far executions to **valid semantic C1**, not to suppress every far execution
or prove another radius cutoff.

The next deciding experiment should keep C1 fixed and deliberately violate
one selected payment constraint, allow legal adaptive C2/point/final choices,
and investigate a joint relation/query upper bound for that invalid-C1 class.
Include the unchanged valid-C1/far-D control. A bound based only on final
distance or optional-object absence will not settle that question. Concrete
encoder/left-inverse and actual opening/replay instantiation can advance in
parallel, but should not be presented as the missing accepted-payment bound.
