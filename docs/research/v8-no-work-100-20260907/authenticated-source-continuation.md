# Authenticated early C1, natural chord image and decoded-note endpoint

Research continuation from `3a0b144dee108041320a23850ab4478444a74745` on
`research/v8-no-work-100-20260907`. The previous turn made verified progress
and published it. This turn started with a clean research worktree and reuses
that work unchanged. Main and production remain untouched. During the proof
runs main was `9b84a1e27d2159ca21fc4ed9dad21b5a9e87daf1`; the final read-only
check observed `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, with its unrelated
untracked V7 CU result directory preserved. Imported source/cache provenance
was checked against the research pin, not inferred from main's moving HEAD.

## New connections and the remaining end-to-end claim

The target is still acceptance by the complete repaired verifier **and failure
of a specified bounded extractor to return a checked payment witness**. Neither
a missing radius classifier nor the absence of an early Merkle path is silently
identified with that failure.

This continuation works on three actual gaps in that path:

1. Construct the early C1 word from a finite chronological hash-answer prefix,
   and derive accepted-opening agreement or an explicit hash failure event.
2. Relate the literal two sparse image claims to the natural circle-code space,
   and distinguish the actual natural-coordinate projection from monomial
   truncation before connecting chord reconstruction to point evaluation.
3. Derive owner/input-note/nullifier hashes from the selected decoded cells and
   individual residuals, then use the already-proved 24-level membership path.

No new probability is assigned to deterministic correspondence. The existing
conditional row ceiling is unchanged. Global arbitrary-oracle recovery,
operational extraction, complete source/payment/Fiat–Shamir correspondence and
full-view privacy remain obligations, not a numerical certificate.

## Authentication no longer assumes every early path exists

`AuthenticatedEarlyC1Prefix` takes an ordered list of raw hash inputs and their
208-bit answers, and the C1 root. Its frozen view uses only those answers; a
missing input gets a fixed default. The V7 partial-path resolver then defines
a deterministically totalized C1 word and the original `earlyC1` option. No later hash answer,
C2 choice, final polynomial or sampled opening position enters that definition.

The proof relates this finite-prefix view to a later consistent oracle only
on inputs actually present in the prefix. It does **not** assume equality of
the two total hash functions or that a root alone reveals a full word.

For each actual bottom-up root-authenticating C1 opening, V7's per-opening
path and binding lemmas derive one of:

```
opening is a projection of the early canonical C1 word
OR its path includes a new hash input hitting an early unresolved target
OR the shared raw-input log contains a 208-bit digest collision.
```

The actual authenticating path is built from the supplied siblings. The proof
is not a q16 wrapper, and it applies when the position is selected later.
Trace inclusion and consistency of the observed hash answers remain explicit.
`TraceIncludedInLog` is membership inclusion, not chronology: the actual
chronological source prefix still has to be constructed in the experiment.

`AuthenticatedEarlyC1Projection` uses this alternative on a supplied set S of
root-authenticated, canonically decoded matching fibres. If |S| is at least
245609, it identifies the original prefix-fixed C1 option with the tuple's C1
projection, **or** retains a late-target-hit/collision event. It does not assume
that every early path resolved or that the option was already `some`.

Those S openings are a **strong sufficient access control**, not a mandatory
lower bound on extractor reads or extra values in a q22 proof. One proof does
not disclose them. The theorem does not supply the replay algorithm, its
fixed-root coupling, its success probability or its running time.

There is a less demanding intended composition: instantiate near-gamma on
the **same prefix-totalized C1 word**, with C2 fixed at its own legal later
boundary. Its componentwise own support can feed `EarlyC1LateProjection`
directly. Only the actual verifier openings then need coupling to that word
outside the shared hash events. This does not upgrade default-zero values
into authenticated openings and does not use the stronger S theorem's access
premise. The concrete received-word/source-game construction is still missing.
Near-gamma support alone neither supplies S nor supplies an efficient decoder.

### One fixed target set, even with adaptive opening positions

`AuthenticatedEarlyC1Targets` constructs the set of first-unresolved targets
over **all** 262144 possible C1 fibre positions from the same early prefix/root.
Its cardinality is at most 262144. This is proved using symbolic list lengths,
not by reducing the full domain.

Every per-opening late-target event implies a fresh input in the shared later
log hits that single early target set. Thus a later adversarial choice of
opening position cannot enlarge the set or require pretending that position
was fixed before its actual selection time. The raw collision is shared too;
it should not be counted afresh per opening or per recovered tuple.

The next probabilistic interface is explicit: in the stipulated ideal raw-hash
oracle experiment, after conditioning on a genuine chronological prefix,
fresh distinct raw inputs must receive conditionally uniform outputs, with a
declared count of later queries across all applicable
replays/forks. The generic V7 budgeted-target theorem is relevant; its old
numerical target caps are not the new whole-domain cap. No unproved source
coupling or 104-bit birthday-work estimate is substituted for that experiment.

## The image claims concern the unprojected natural reconstruction

Write the y-low-bit tensor as q[2j]=A_j and q[2j+1]=B_j, with
`phi_j = product of T_(2^bit)` over j's set bits. The full polynomial pair is

```
E = a*A + b*X*A + c*(1-X^2)*B
O = c*A + a*B + b*X*B.
```

`ChordPolynomialImage` proves evaluation equals
`(a+b*x+c*y)*(A(x)+y*B(x))` **on x²+y²=1**. Its quotient/reconstruction
equivalence additionally requires a nonzero chord denominator, while the
received value itself is arbitrary. Dropping the circle equation is false:
Q=y and chord=y reconstruct to 1-x², which is not y² off the circle.

The same leaf proves, symbolically in the degree cap, that the full pair has
original-code degree exactly when its two high-coefficient obstructions vanish,
provided (b,c) is not (0,0). A low-degree interpolant leaves that condition
unchanged. This does not prove the actual sequential OOD answers are correct.

The selected source supplies chord nondegeneracy through its checked slope
inverse: in the unequal-x branch c=x1-x0 is nonzero; in the equal-x branch the
inverse of y0-y1 requires b to be nonzero. Identical points reject. Actual
whole-domain denominator liveness is separate from checking queried inverses.

`NaturalLineBoundary` proves the degree/top-coefficient and low-bit identities
symbolically. `NaturalChordImage.selected_image_iff` then proves the exact
selected condition:

```
degree(E) <= 511 AND degree(O) <= 511
IFF q[1023]=0 AND b*q[1022]-c*q[1021]=0.
```

The key basis identity is phi_511=X*phi_510, so their leading coefficients
are equal and nonzero. The result concerns the full unprojected polynomials;
discarding overflow first would not establish it. No received oracle is
assumed globally polynomial by this lemma.

[NaturalChordProjection](natural-chord-projection-review.md) constructs the
total conversion at width514 using V7's proved nonsingular natural coefficient
matrix, then takes the first512 natural coefficients. It proves this extended
representation captures the entire chord product even when the image is
invalid. On an image-valid result the projected polynomials equal the full
ones, and their evaluation is exactly chord times quotient on the circle.
The padding/prefix adjoint is proved without an assumed rank or transpose
identity. Packaging the pair into the actual interleaved `Rows.reconstruction`
and proving equality to the optimized Rust carry/transpose remain separate.

An important total-map distinction is preserved: the source zero-pads its
original natural covector and transposes full chord multiplication. Therefore
the ordinary reconstruction is natural-coordinate projection of that product,
not monomial truncation. For example at width2, x²=(phi_2+1)/2: natural prefix
projection returns 1/2, whereas monomial truncation returns zero. They agree
on an appropriately proved image-valid low-degree result, not on all inputs.
An invalid-image game's prior must still use the correct total operator.

## The selected decoded key now reaches the note and nullifier hashes

[SelectedNoteRecovery](selected-note-recovery-review.md) derives, from explicit
selected residuals in the maintained field/hash model:

```
row11 = ownerHash(key at row12)
row59 = noteHash(ownerHash(key), amount at row44, asset, split salt)
row427 = nullifierHash(the same key, the same salt).
```

It constructs the intermediate round chains rather than assuming their
correctness. The note equality replaces the formerly unclassified starting
digest in the selected 24-level path, yielding the recorded forest endpoint
at row907. Optional literal asset/nullifier residuals connect the hashes to
caller-provided parameters; they do not authenticate those parameters.

The six required zeros at row60 columns2–7 are selected note-framing equations,
not arbitrary relation-free mask cells. No padding constraint is removed to
make a fixture pass. The returned key is a concrete decoded value, not a
supplied `validWitness` or ownership predicate.

Remaining endpoint work includes literal Rust round/constants refinement,
amount positivity, output-note and transition reconstruction, path/occupancy
index composition, authoritative context and settlement. Acceptance enforcing
the individual equations is still an upstream probabilistic/source obligation.

## Total accounting and cost

| Stage/event | New information | Still required |
|---|---|---|
| Accepted C1 opening differs from early word | Derived late hit on one early target set or shared raw collision | Actual chronological source trace, uniform fresh-raw-query law and bounded resources |
| Qualifying supported tuple's early C1 | Authenticated matching support identifies the unchanged option, or explicit hash failure | Obtain sufficient support/openings within the extractor's resources |
| Chord/image/relation | Full polynomial image condition and circle evaluation; natural truncation must be used | Concrete coefficient/source accumulator and encoder interfaces; causal anchor coverage |
| Decoded note and nullifier | Same concrete key/salt determines both and the membership-path input | Literal implementation, full payment/context/settlement validator |
| Accepted outside/none/replay failures | No failures discarded or assigned zero | Global residual recovery bound, abort/fuel/missing-response accounting |
| Fiat–Shamir and hiding | No messages or nonce powers changed | Resource-bounded FS and adaptive full-view simulation |

The earlier near-gamma, row, image and post-query events overlap. Nothing here
adds their bounds together or charges the four relation repairs twice. The
global bound and remaining global error allowance remain unspecified.

Body: `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
No verifier, transcript, Rust, SBF or production edits; no new proof-body
values or verifier operations. Prior performance evidence is unchanged, not
remeasured. Extractor oracle reads and formal-proof resource measurements are
not transaction CU or proving-time measurements.

## Focused evidence and next decision

The [machine evidence](authenticated-source-evidence.json) audits current
source hashes, successful logs, generated olean hashes and each named axiom
audit. All retained results use only standard axioms: `propext`,
`Classical.choice`, `Quot.sound`. No `sorry` or new axiom is retained.

| Final focused leaf | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| AuthenticatedEarlyC1Prefix | 0 | 4.30 | 5,678,972,928 | 0 |
| AuthenticatedEarlyC1Projection | 0 | 3.12 | 5,659,131,904 | 0 |
| AuthenticatedEarlyC1Targets | 0 | 3.06 | 5,659,017,216 | 0 |
| ChordPolynomialImage | 0 | 4.35 | 5,662,801,920 | 0 |
| NaturalLineBoundary | 0 | 5.32 | 5,626,691,584 | 0 |
| NaturalChordImage | 0 | 4.71 | 5,620,645,888 | 0 |
| NaturalProjectionCore | 0 | 3.17 | 5,650,923,520 | 0 |
| NaturalChordProjection | 0 | 3.36 | 5,640,585,216 | 0 |
| SelectedNoteRecovery | 0 | 3.74 | 5,646,073,856 | 0 |

Lean4.32.0 / Mathlib81a5d257 caches were reused, with source/import/output
pins in the logs. Jobs ran serially with `-M7000` and a separate7GiB
aggregate descendant RSS guard. No cold build or unchanged full replay ran.

### Failed preflights and their actual repair

The first two generic chord attempts failed on local noncomputable-definition
and whitespace-sensitive notation errors (`<m`/`≤m` parsed as matroid
notation). After fixing the source, `chord-polynomial-v3.log` passed. These
were local Lean errors, not failed mathematical claims.

The natural specialization then exposed a concrete-reduction problem:

| Failed natural-image log | Exit | Wall seconds | Peak RSS bytes |
|---|---:|---:|---:|
| v1 | 134 | 12.50 | 7,548,141,568 |
| v2 | 137 | 10.46 | 7,536,738,304 |
| v3 | 137 | 10.43 | 7,542,718,464 |

The first failure involved concrete basis unfolding; replacing it with a
generic low-bit recurrence did not alone settle specialization. The generic
boundary file was then split out and checked first. Specializing the proved
recurrence by direct definitional equality still caused expansion of concrete
polynomial heads. The final repair uses an explicit field parameter and
named numeral rewrites on the already-typed theorem before specializing at
255. It does not ask the kernel to reconcile expanded phi_511/phi_510.
That changed source passes in4.71s at5.62GB; no cap was raised or unchanged
memory-killed job rerun. Failed logs are kept, not counted as proof evidence.

The authentication/note reports preserve their small parser/list/row-index
preflight errors separately. The projection core and dependent projection
both passed their first focused run. Unchanged adversarial fixtures, SBF
tests and previous Lean manifests were not replayed.

Reproduce only changed leaves, in dependency order and with fresh log names:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_polynomial_image.sh ChordPolynomialImage /absolute/NEW-chord.log
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_polynomial_image.sh NaturalLineBoundary /absolute/NEW-boundary.log
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_polynomial_image.sh NaturalChordImage /absolute/NEW-image.log
python3 docs/research/v8-no-work-100-20260907/experiments/audit_authenticated_source.py --check-recorded
```

Authentication, projection and note runners are documented in their linked
subreports. The complete new recorded evidence passes the read-only audit.

The next decisive experiment is to construct the actual chronological V8
C1 exposure prefix and inject the current verifier's openings into the shared
early-target/collision classifier, using that **same** completed word as the
near-gamma/early-semantic received word. It must retain the correct C2 timing
and all replay/fuel/missing-response outcomes. This tests the source coupling
without imposing245609 actual reads as a new requirement. Efficient bounded
coefficient recovery and the far/uncovered algebraic event still need their
own arguments, as do the remaining payment/FS/privacy interfaces.
