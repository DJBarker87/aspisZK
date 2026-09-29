# R60: concrete inverse chain and circle-policy bridge

Base: `eb51ef6ea5be51585ee40da75a86567b92c1575e` (pushed R59).
Branch: `research/v8-r60-inverse-chain-20260929`.
Formal/source-audit milestone only; verifier and protocol unchanged.

## Result

**23 new Lean theorems compile**, with 23 standard-axioms audits. The exact
M31 inverse addition-chain schedule now has a universal canonical-word proof,
using the retained raw reducer rather than assuming an inverse primitive.
That chain supplies the base inverse in the source-shaped CM31 and QM31
norm/conjugate formulas. Their field meanings are proved correct, including
nonzero norms. The resulting guarded circle map equals R54's mathematical
policy, and its bounded program inherits the existing coherent memoized-oracle
law with unchanged errors, state and hash trace.

This is **not yet a universal proof of actual Rust field/sampler execution**.
The exact remaining source bridge is stated below. No full privacy/soundness
or independent-uniform challenge claim is made.

## Base inverse without an assumed inversion oracle

`InverseChain.lean` defines repeated squaring and the literal source chain:

`t2 → t4 → t8 → t16 → t24 → t28 → t29 → t30 → result`.

The first six named values have exponents `2^k−1`; the last operations yield
`4*(2^29−1)+1 = 2^31−3 = P−2`. The proof manipulates symbolic powers, not a
concrete expanded field recurrence. It also proves that this schedule commutes
with any multiplication-preserving map.

Canonical words are `Fin P`. Their multiplication is the retained
`RawReducer.rawM31Mul`, whose canonical-output and residue theorems are reused.
Thus every intermediate stays canonical, and the word chain decodes to
`x^(P−2)`. The already-proved primality of P and Fermat's theorem identify this
as the inverse for every nonzero canonical word. The zero guard and successful
nonzero result are explicit; zero is not silently mapped to a valid inverse.

`audit_r60_source.py` parses the actual Rust assignments and Lean assignments
into the same restricted multiplication/squaring syntax tree. It checks all
nine bindings, the exact square-loop body, zero assertion and **38 base-field
multiplications**. It rejects five changed-schedule/guard mutations. Both the
repository source and selected R59 staged source match. This structural audit
is evidence about the operation schedule, not a verified Rust parser/extractor
or proof of generated range-loop execution.

## Norms and circle map

`NormInverse.lean` reuses the exact deployed tower and its retained nonsquare
proofs (`i²=−1`, `u²=2+i`). It defines the base inverse through the word chain,
then the source-shaped formulas:

- CM31: norm `a²+b²`, output `(a,-b)/norm`;
- QM31: norm `c0²−(2+i)c1²`, output `(c0,-c1)/norm`.

The norm of a nonzero element is nonzero at both levels. Consequently these
formulas equal mathematical inversion without a new nonzero-norm assumption.
`tryInverse` returns none exactly on zero and the inverse otherwise.

The resulting map computes the inverse of `1+t²`, returns the singular error
if absent, then checks the CM31-subfield policy. Its output and ordered errors
equal `SamplerCirclePolicy.pureMap`. The chain-based accept function and
bounded circle program equal their R54 counterparts, yielding the existing
memoized-oracle program law. This does not make challenges independent after
conditioning on later roots, failures, retries or publication.

## Compiled evidence and resources

| Target | New theorems | Wall seconds | Peak RSS KiB | Exit / swaps |
|---|---:|---:|---:|---|
| InverseChain | 10 | 1.69 | 3,271,980 | 0 / 0 |
| NormInverse, including program bridge | 13 | 1.72 | 3,274,720 | 0 / 0 |

All new axioms audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Lean 4.32.0, focused `lake env lean`, cached workspace; 295 successful
source-pinned objects in the final cache. Two missing current split reducer
dependencies compiled once: RawReducerNat, 0.48 s / 550,924 KiB; RawReducer,
0.96 s / 1,889,140 KiB. Both exit 0, zero swaps, four audits each.

The older R17 unsplit reducer object was **not reused** after the source-hash
check found a different layout. A runner path typo was fixed before compiling.
The first chain proof hit a tactic recursion limit because a reverse `pow_one`
rewrite recurred; it was replaced by terminating power-successor rewriting,
not a raised recursion/memory limit. Two norm/bridge proof attempts had local
rewrite/identifier errors. Failed logs and source hashes are retained; only
final exit-zero, no-sorry artifacts count as compiled evidence. Unchanged
successful dependencies were reused between attempts.

NUC scopes: MemoryHigh=3G, MemoryMax=5G, MemorySwapMax=0, TasksMax=128.
Maximum simultaneous reserved memory 5 GiB. Collection used 1G/2G. No cold
dependency build, generated aggregation, package replay, Rust rebuild or SBF
rerun. No runtime source changed, so repeating unchanged runtime regressions
would add no coverage to these proof edits.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r60_evidence.py
```

The checker authenticates the current Lean sources/cache records, successful
logs/axioms, failed attempts, exact selected runtime manifest, chain syntax
audit and norm-function source bodies. Evidence is under
`evidence/r60-inverse-chain`. No production change, negative-regression removal,
new hiding premise, deployment, merge, transaction or wallet/key operation.

## First remaining proposition

Prove the actual generated/word execution of `square_n` and the guarded M31
inverse refines `InverseChain.guarded`, then compose the CM31/QM31 word-level
norm, negation, multiplication, equality and try-inverse branches with
`NormInverse`. The authenticated R17 generated arithmetic results are useful
predecessors, but the selected optimized multiplier and actual iterator/error
semantics must be connected rather than assumed equal. The new schedule audit
and raw-word theorem do not close that extraction/refinement step.

After that: compose actual sampler execution with the full prover/observer
chronology. Joint commitments, shared-oracle/seed expansion, all semantic and
opening disclosures, retained posterior/simulator construction, failures,
retries/publication and explicit justified loss bounds remain obligations.
Coherent pre-beta quotient extraction remains a separate soundness task.
The earlier C1 negative, fixed-block hiding and local joint-view coverage
results retain their distinct scopes.

CU stays at the measured R59 **1,516,838 / 1,518,195**, with both actual 1M
runs exhausted. The 518,195-CU gap and the next mixed-width opening/ordinary
caller optimizations remain tracked independently of the privacy proof.
