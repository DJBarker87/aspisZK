# V8 scalar-fingerprint and prefix-causality evidence

Date: 2026-09-07  
Implementation/formal commit: `2bddfcb4` (`formal: bound v8 scalar-fingerprint gamma family`)

## Decisive result

The no-new-tree verifier authenticates 29 public component values at each of
two OOD points, but its algebraic check observes only one gamma dot per point.
Parser/prefix replay can therefore prove that all branches reuse the same
public vectors; it cannot prove that an extracted tuple is component-wise
equal to them from those scalar checks alone.

`V8A100ScalarFingerprintGammaBound.lean` proves the sound replacement:

- each nonmatching tuple passes both scalar checks at at most 28 nonzero
  gammas;
- the actual fixed tuple family has cardinality at most 100, so the
  unconditional bad-gamma set has cardinality at most `100 * 28 = 2800`;
- this includes the case in which no tuple has the complete public
  fingerprint;
- only when an exact fingerprint anchor is known to exist does the alternative
  set sharpen to `99 * 28 = 2772`;
- a constructive two-gamma interpolating vector refutes the inference from
  scalar agreement to component-wise equality.

The Rust API now retains the two absorbed vectors inside `V8A100OodPrefix`,
keeps `V8A100TwoPointChallenges` fields private, and constructs challenges
only from that retained prefix. The production-facing from-wire constructor
rechecks packed-field canonicality before transcript absorption, including
for a wire returned by the deferred parser.

## Focused Lean replay

Command, from `AspisFormal/` in the research worktree:

```sh
LEAN_PATH="$(cd /Users/dominic/ZK/AspisFormal && lake env printenv LEAN_PATH)" \
  /usr/bin/time -l \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  AspisFormal/V8A100ScalarFingerprintGammaBound.lean
```

Result: exit 0; 4.94 s real; maximum resident set size 5,348,524,032 bytes;
0 swaps. The high imported-dependency footprint stayed below the repository's
8 GiB local focused-build limit.

Every retained `#print axioms` result was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This applies to:

- `scalarFingerprintMatchSet_card_le_28`
- `twoScalarFingerprintMatchSet_card_le_28_of_mismatch`
- `twoGammaInterpolatingVector_at_alpha`
- `twoGammaInterpolatingVector_at_beta`
- `exists_fixed_public_vector_matching_two_branch_scalars`
- `nonmatchingScalarGammaSet_card_le`
- `full_fingerprint_of_scalar_match_outside`
- `scalar_match_mem_nonmatching_of_no_exact_match`
- `nonmatchingTupleScalarGammaSet_card_le`
- `fixedWidth29_nonmatching_scalar_gamma_card_le_2800`
- `alternateTupleScalarGammaSet_card_le`
- `fixedWidth29_alternate_scalar_gamma_card_le_2772`

There is no `sorryAx`, new axiom, `admit`, or unsafe proof escape.

An earlier focused attempt timed out while elaborating nested `Finset.biUnion`
membership over the concrete `Fin 29 -> InitialMessage` type at the default
200,000 heartbeats. It was not retried with a larger heartbeat allowance.
The proof was factored through a generic candidate-family theorem; the final
replay then completed at the default heartbeat limit.

## Focused Rust replay

Command, from the research worktree root:

```sh
/usr/bin/time -l \
  cargo test --locked --release -p aspis-core v8_ -- --nocapture
```

Result: exit 0; 0.28 s real on the warm release cache; maximum resident set
size 82,280,448 bytes; 0 swaps. Tests: 16 passed, 0 failed, 1 intentionally
ignored profiling gate. The passing set includes
`wire_derived_prefix_is_the_only_public_challenge_constructor`, which checks
wire/prefix/challenge vector identity and rejection of a deferred-parser wire
with a noncanonical packed M31 limb.

## Remaining source-connected boundary

The existing `Tag73K12ParsedProof` is V7-specific: it has
`QuerySchedule 16 262144` and no component OOD vectors. The V7 raw message
type has only `oodValue : Fin 2 -> Qm31Bytes`. A production source theorem
therefore still requires a V8-specific 697-QM31 raw/parsed proof and a
translated accepted quotient classifier that supplies these scalar facts for
each restored branch:

```lean
width29Batch (componentOodVector extraction.components zeta0) gamma =
  width29Batch parsed.componentOodVectors.0 gamma

width29Batch (componentOodVector extraction.components zeta1) gamma =
  width29Batch parsed.componentOodVectors.1 gamma
```

The existing scheduler-native gamma consumer already handles both cached and
fresh/advance oracle coordinates. The missing work is carrying the fixed
parsed vectors through that replay and proving the two scalar acceptance
facts; it is not a scheduler cache-model redesign. Digest-state equality by
itself must not be used to infer vector equality.
