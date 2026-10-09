# Fixed-Q fold support closure

This checked continuation addresses the deterministic interface for a collector
holding different pointwise observations from different alpha branches.
It does not prove a probability of obtaining those observations.

## Exact statement and what it changes

`FoldSupportClosure.lean` first compares two arbitrary four-slot received
words at one fibre. Their actual normalized folds are evaluations of
degree-at-most-three polynomials in alpha. Equality at four distinct alpha
values makes these polynomials identical; the existing exact radix-four
inverse then identifies all four raw slots. No polynomial representation of
the global received oracle is assumed.

The selected specialization uses the literal natural1024 encoder,
canonical log20/log18 four-slot index map, canonical inverse tables and
natural256 final encoder. For one already reconstructed Q and branches
already identified with its coefficient folds, it proves:

1. Four distinct matching identified alphas at a fibre imply full Q/R slot
   equality there.
2. With at least four identified alphas overall, that multiplicity condition
   is equivalent to full Q/R slot equality. Agreement with every identified
   alpha is equivalent to the same condition.
3. A finite `observedClosure` takes differing per-alpha observed supports
   and retains fibres observed on at least four distinct identified alphas.
   When each supplied observation is an actual pointwise match, every
   retained fibre is certified full-slot support for Q.
4. Any further adaptive final whose valid observed support overlaps this
   closure on more than 255 fibres equals the corresponding fold of Q.
   This consumes the previously proved exact selected final-code overlap
   cap, not a caller-supplied encoder equality.

Thus the complete mathematical matching sets do **not** gain new geometric
support: multiplicity-at-least-four, the full intersection of all coherent
matching sets, and Q's full raw support coincide. The advance is an
observation/access interface. Different branch observations can certify
different fibres without having supplied one observed set shared by every
branch. The closure is defined from those finite observed sets; there is no
full-domain enumeration in this construction.

## Scope and remaining collector obligations

Q and initial final identities remain prerequisites here; this leaf does
not reconstruct an initial seed without them. Earlier four/seven-alpha
results can supply such a seed when their hypotheses hold. Finals may be
chosen adaptively after their alpha challenges. The polynomial argument is
deterministic after fixing Q and the observed branches; it is not a root
probability for a postselected Q.

The observed-set validity premise is literal pointwise agreement with the
same mathematical received word. Cryptographic authentication, fixed-word
coupling, replay access, and deriving pointwise agreement from scalar
acceptance with all collision events charged remain separate. So do the
probability/resource cost of collecting an initial coherent seed, fourfold
observation multiplicity, and the >255 overlap for each extension. No
uniformity of accepted or retained queries is assumed.

The source maps are reused from pinned V7/V5 formalisation. No V7 raw-word
consistency predicate is substituted for the V8 quotient/fold relation.
No image or ordinary-row correctness is concluded by this closure leaf;
those remain the distinct three-tau/four-kappa deterministic endpoints and
their still-required quantitative access argument.

No protocol, proof-body or verifier source changed. The body remains
40,282 bytes. This laptop-only Lean work measures neither proving time nor
complete-transaction CU. No NUC or external job ran.

## Evidence

Research revision: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`.
Borrowed source closure: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Concurrent main was read-only at `946ade6f86854c46b24a0291a5ce115749139a16`.
Mathlib pin: `81a5d257c8e410db227a6665ed08f64fea08e997`.
The runner audits source bytes and cached olean hashes of the imported
research/V7/V5 closure before and after the focused check.

From the research worktree, using a fresh log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_fold_support_closure.sh docs/research/v8-no-work-100-20260907/experiments/fold-support-closure-replay.log
```

The command uses the cached `lake env lean` environment with Lean 4.32.0,
`-M7000`, and a serialized 7-GiB aggregate child-RSS guard. No dependencies
are rebuilt.

| Replay | Exit | Lean wall | Peak RSS | Swaps | Result |
|---|---:|---:|---:|---:|---|
| `fold-support-closure-v1.log` | 1 | 35.38 s | 5,202,427,904 B | 0 | Local degree-coercion, classical filter decision and reserved-identifier fixes required |
| `fold-support-closure-v2.log` | 0 | 30.02 s | 5,524,455,424 B | 0 | All seven audits standard-only; full postflight passed |

The v1 failure is retained. V2 changed only the proof elaboration: an
explicit Nat-degree intermediate, local classical decidability, and the
identifier `matchedAt`. No mathematical hypothesis or resource cap changed.
The retained source contains no `sorry` or new axiom. Every retained audit
lists only `[propext, Classical.choice, Quot.sound]`; failed v1 declarations
are not claimed results.

Frozen SHA-256 values:

- Source: `6533b4b6ad8c232c4a8bd87e13f2de7837dd125b316a257d2b7dea4bb968963d`
- Olean: `a2fddf05f2887f0468b4b4b6e017612dbfed10e4a01839735103336987544926`
- Runner: `22599bb4381952d126acde6a998b2179482424bd4fa1743ac7ff4d07c393b95d`

The decisive next use is a collector that supplies an initial identified
seed and these differing observed supports with explicit replay/authentication
provenance, then proves sufficient closure overlap at bounded cost. The
present result is the deterministic algebraic interface for that task, not
its availability theorem or a numerical global security certificate.
