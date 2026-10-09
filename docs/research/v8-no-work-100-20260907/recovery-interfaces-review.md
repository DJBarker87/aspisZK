# Recovery support and the literal decoder/parser interfaces

Continuation base: `503332fbe747db381fc8ee67c4bbdd3631ec97cf` on
`research/v8-no-work-100-20260907`. Production and concurrent main work are
unchanged. This is progress toward the same global checked-payment extraction
objective, not a replacement goal consisting of a smaller local bound.

## What changes mathematically

The completed `HelperJointGame.early_c1_wrong_claim_bound` is reused unchanged.
It bounds a specific accepted-wrong-C1-claim event in the supported final
distance-at-most-15,334 region, given the actual early C1 tuple. Its ideal
bound `53/(k-1)+24/k`, approximately 117.7332 bits, is neither the whole near
regime nor global extraction failure. The present continuation does not
replay it or add another overlapping relation-repair term.

The new support bridge addresses an actual prerequisite of using older V7
recovery beyond that region. From an image-valid quotient candidate, at
least **26,095 quotient-matching fibres** suffice to retain at least **9,558
complete fibres / 38,232 original-domain symbols** after excluding at most
16,535 C1-bad fibres and two pole fibres. `HelperSupportTransfer` constructs
the retained set, proves literal normalized-helper agreement there, and
uses the real log20 circle encoder. It does not treat the restricted support
as a different code. The 26,095 cutoff is a conservative sufficient bound,
not a necessary or globally optimal one.

The support leaf passed its first focused replay. The actual accepted
candidate and this support must still be produced by a
soundness argument. Merely substituting degree two for degree 28 in the old
recovery theorem does not do that. The exact old-formula control gives only
79.55 gamma bits; one improved inner-dimension control gives 81.50. Even
their mathematical ports are not established here. See
[the support audit](helper-support-transfer-review.md) for precise hypotheses
and the support-loss falsifier. No old approximately 75-bit loss has been
reintroduced as an applicable V8 bound.

### Why subtracting C1 at the quotient level needs extra care

The root task follows the actual sparse OOD interpolant rather than an
illustrative raw claim polynomial. Fix both received words to zero before
their commitment boundaries. At both sequential OOD responses claim lane zero to be one and
all other lanes to be zero; these answers do not depend on the later gamma.
Keep the sampled OOD coordinates and their checked inverse untouched.

The actual interpolant is then the constant one. At every nonpole source
symbol the virtual quotient is `-1/L`, even though all three received helper
words are zero. Scaling away the C1 lane offset produces

```
gamma^(-26) * (-1/L).
```

For a fixed quadratic `P`, equality with that expression implies that
`X^26*P - C(-1/L)` vanishes at gamma. Its constant coefficient is nonzero
and its degree is at most 28, so there are at most 28 matching nonzero
parameters. `QuotientHelperShift` connects this symbolic fact to the actual
OOD and selected encoder definitions. The complete leaf passed its focused
v2 replay with standard-only axioms, without a resource-cap increase.

This is a new source-level instantiation of the earlier warning about false
C1 claims: it specifically disproves an unshifted quadratic representation
of the virtual quotient. It does not claim the false OOD responses pass the
repaired relations, or that this zero-word fixture is a valid payment. The
legitimate alternatives are to retain the known reciprocal-power shift, or
to reconstruct an image-valid **original** polynomial and normalize it on
the actual C1 support. The new support theorem proves the latter interface,
but not the missing acceptance-to-candidate implication. Neither proof-only
alternative adds proof values or verifier operations.

## Deterministic source and witness progress

The generic `DecodedIndex32` theorem models the actual UInt32 OR/shift
recurrence, not unbounded-integer arithmetic alone. For 20 parsed bits the
value is below `2^20`, every low bit has its original value, and all higher
bits are false. The dependent `SelectedMembershipDecode` has also passed.
Canonical raw C1 and individual modeled path/copy residuals establish all24
successful direction parses, the actual sibling reads, and the decoder's
one-pair +20-lane +3-forest path. The same table supplies the selected input
note, owner key and nullifier, and the literal row907 binding relates the
constructed path to an independently supplied public root. Neither decoder
success nor a desired path/root is assumed. The actual account authority and
full Rust payment validator remain separate interfaces.

`CanonicalRelationInput` is already checked. Success of a constructed
short-circuit canonical parser supplies all **697** fixed-field decodes,
in-range reads, response offsets `417+6*round+sent`, and final offset 441.
Every malformed body length or noncanonical limb in the fixed section
rejects. The six response values are retained in positions `[0,1,2,3,5,6]`;
only `c4=claim*quarter-c0` is reconstructed, and the existing V7-consumed
compact boundary theorem applies. This avoids assuming a byte/value
correspondence predicate for this model.

These are source-shaped deterministic statements, not a complete translated
Rust verifier. The parser covers the fixed section, not the 621-byte query
record, hashes, Merkle checks, or the entire mutable Wire execution. Hash
round constants, gate translation, actual caller/account context, output
append and exact settlement remain explicit interfaces. No missing source
correspondence is assigned an invented failure probability.

See [the parser report](canonical-relation-input-review.md) and
[the membership report](selected-membership-decode-review.md).

## Accepted-extraction accounting remains total in scope

Let `A` be actual repaired-verifier acceptance and `X` be the specified
resource-bounded extractor returning a witness accepted by the payment,
independent context and exact transition checks. The target remains
`Pr[A and not X]`. The following precedence is an obligation map, not a
claimed completed probability partition:

| Class after source/authentication/replay coupling | Current status |
|---|---|
| A checked witness is returned within the declared resources | No extraction failure, regardless of radius or provider label |
| Early C1 exists; final distance <=15,334; a C1 ordinary/OOD claim is wrong | Previous causal compact-field bound; source coupling still required |
| Same region, claims correct, but no checked witness returned | Individual early semantic/copy constraints, actual decoder, and full payment/context endpoint still needed |
| Early C1 exists; final distance >15,334; extraction fails | New deterministic support bridge, but no new accepted-mass bound |
| Early C1 is absent and extraction fails | Still uncovered; absence of all26 lanes must not be equated with unrecoverable semantic16 |
| Private coefficient-decoder failure with its ideal access/law prerequisites | Previous conditional bound reused, not silently connected to authenticated replay |

Source mismatch, malformed authentication, abort/fuel, missing responses,
cached/advanced challenge mismatch and all provider-none outcomes must first
be coupled to the actual extractor. Scalar acceptance with failed pointwise
checks remains part of the probability game; the shifted degree-q rho and
four sequential relation repairs are not removed. The family/object
existence lemmas remain distinct from a bounded executable extractor.

The new diagnostic `choose(16535,22)/choose(262144,22)` is about 2^-87.7277:
all fresh public queries can lie in the C1-excluded set. It is **not** an
extraction-failure probability. Charging the entire event as a failure would
miss 100 bits; assuming it harmless would also be unjustified. The remaining
argument must use its relation/claim constraints or actual witness recovery.

The original/paired root products, high-J own-support case, T512 invalid
image, zero-fold image kernel, unshifted-row and late-inactive failures,
shifted-query/later-repair collisions, harmless out-of-radius corruption and
mask-only full26-versus-semantic16 distinction remain regressions. No
unchanged heavy experiment was rerun or reclassified as a forgery.

## Evidence and cost scope

Focused evidence is generated by `experiments/audit_recovery_interfaces.py`.
[The evidence JSON](recovery-interfaces-evidence.json) records source/olean
hashes, exact targets, exit status, time, peak RSS, swap and standard-axiom
audits for every retained endpoint. All six leaves passed; their 48 printed
declarations use only `propext`, `Classical.choice` and `Quot.sound` (or
subsets). No retained proof introduces an axiom or `sorry`.

| Focused leaf | Green log | Wall seconds | Peak RSS bytes | Swap |
|---|---|---:|---:|---:|
| DecodedIndex32 | decoded-index32-v2.log | 15.62 | 5,568,364,544 | 0 |
| SelectedMembershipDecode | selected-membership-decode-v3.log | 22.91 | 5,583,601,664 | 0 |
| CanonicalCollect | canonical-collect-v2.log | 2.38 | 1,265,254,400 | 0 |
| CanonicalRelationInput | canonical-relation-input-v2.log | 11.40 | 5,608,521,728 | 0 |
| HelperSupportTransfer | helper-support-transfer-v1.log | 13.66 | 5,720,850,432 | 0 |
| QuotientHelperShift | quotient-helper-shift-v2.log | 17.69 | 5,731,319,808 | 0 |

The root v1 failed on an implicit `natDegree_mul_le` argument, an unexpanded
`IsRoot`, a namespace-ambiguous slope/circle evaluator, and a broad
definitional comparison of concrete field expressions. The replacement
uses explicit typed polynomial inequalities, the evaluation goal, qualified
names and a named unchanged-denominator equality. No giant field reduction,
increased heartbeat/recursion cap, altered statement or added hypothesis was
used. V1 is retained as a failed diagnostic; its temporary elaboration
`sorryAx` is not in the green result. Parser/membership failures and their
symbolic replacements are recorded in their linked reports.

Two runners had a redundant blank line at EOF removed during the final
whitespace check. The evidence records both their executed and current
hashes; no proof source or command changed, so no unchanged replay was run.

Reproduction uses fresh log names for any justified changed-source replay:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_decoded_index32.sh /tmp/decoded-index-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_membership_decode.sh /tmp/membership-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_canonical_relation_input.sh CanonicalCollect /tmp/canonical-collect-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_canonical_relation_input.sh CanonicalRelationInput /tmp/canonical-input-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_helper_support_transfer.sh /tmp/helper-support-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_quotient_helper_shift.sh /tmp/quotient-shift-new.log
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_recovery_interfaces.py --check-recorded
```

The borrowed formal revision stays
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; current main HEAD and dirty
files do not replace per-import provenance checks. Builds are serialized,
cached leaves with `-M7000` and a 7-GiB aggregate child-RSS guard. No cold
dependency, package-wide, Aeneas, SBF or full transaction build is started.

The body is unchanged:

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

No protocol message, verifier check, field/domain/query profile, mask,
transcript label or production default changes. No new CU/prover/extractor
performance measurement is claimed. Full-view adaptive ZK and the actual
resource-bounded Fiat–Shamir lift, including nonce/retry/prequery/fork costs,
remain open. No positive grinding credit or quantum claim is introduced.
The global error and remaining release allowance remain explicitly `null`.

## Decision and next discriminating experiment

Keep q22 as the current research direction; this continuation does not
demonstrate its global feasibility or a general impossibility. It closes
literal deterministic interfaces and blocks an invalid low-degree shortcut.

The next mathematical experiment should test a **relation-constrained
three-helper far-final strategy with fixed early C1**, retaining the actual
OOD reciprocal-power shift and counting agreements inside and outside C1's
support separately. The success criterion is a symbolic accepted-wrong-claim
or checked-extraction bound for previously uncovered executions, not another
radius or query-only identity. A reduced causal strategy search must permit
post-alpha finals but not future-query-dependent responses, and record its
restricted/exhaustive scope. In parallel, the next deterministic source
boundary is decoding the packed query record into `SelectedQueryBuffer`;
the next payment boundary is authoritative context/append/afterstate, not
another honest hash round trip.
