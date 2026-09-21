# R16 soundness preservation obligations

## Composed source-shaped opening identity — 2026-09-21

Base `aba46950365f4b90214027d1e1441355b0a61b3f` plus this changeset.
Four focused leaves now connect the previously separate algebraic steps:

- `ChordDual.lean`: finite dot-product padding lemmas and the full-width
  even/odd chord pairing. All 514 positions per output lane remain present.
  The single-scatter extra coordinate is eliminated by its proved support
  bound, while the double scatter retains the complete intermediate vector.
- `SourceChordTranspose.lean`: parity-sum/interleaving identities and the
  source-shaped 1024-coordinate chord transpose, with both weight lanes
  zero-extended from 512 to 514. Its pairing holds for arbitrary q.
- `SourceOpeningResidual.lean`: literal sequential updates at 1023, 1022,
  1021, then the separate ordinary and structured-G channel pairing.
- `TransportedOpening.lean`: composes the result with TransportDual's
  arbitrary-coefficient identity, converting between finite row indices and
  the natural-indexed source-loop model.

The final theorem `transported_source_opening_pairing` states that the
computed quotient-weight dot product is the original-weight dot product on
inverseTransport(sourceChord(q)), PLUS the actual channel residual terms.
There is no honest-generation, legal-mask or residual-zero premise on q.
The theorem parameterizes the public order and inactive set; exact source
inventory correspondence remains required.

The compiled two-channel formula retains precisely:

```
tau   * qR[1023]
+ tau^2 * (b*qR[1022] - c*qR[1021])
+ tau^3 * qG[1023]
+ tau^4 * (b*qG[1022] - c*qG[1021]).
```

These are not silently set to zero. The combined image check still needs
the ordinary/carried-error term and its degree-4 accounting from the retained
two-channel argument. The pairing is deterministic algebra, not a root-count
or Fiat--Shamir distribution theorem.

Crucially, weight zero-padding proves a pairing with the retained low 1024
forward coefficients even if the four high output coefficients are nonzero.
This does not prove high-tail-zero acceptance or that a malicious quotient
lies in the required image. The audit's high-tail assertion is not inherited
as an assumption. That distinction preserves the separate image soundness gate.

Rechecked local r16_basis_transport.rs SHA-256
`36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`;
local and v19 staged r17_opening_weights.rs are identical at SHA-256
`bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
This is a mathematical model of that source shape, not an extracted Rust
execution proof. Original weights, the source field embedding/word operations,
array reads/writes and the concrete fixed inventory remain source obligations.

First remaining source-specific proposition: `original_weights` and its
WeightAccumulator/structured-mask materialization, together with the actual
field/array implementation of the composed pipeline, realize this identity
for both channels and arbitrary extracted coefficients. Commitment extraction,
image validity, all folds/final openings, adaptive challenges and explicit
soundness loss still require their own proofs. The joint legal C1/H1/G
coverage and full-transcript privacy gates are unchanged, not discharged.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; each leaf compiled
with `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured with `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ChordDual, initial partial-application simplification | 1 | 8.55 | 1427341312 | 0 |
| ChordDual, explicit unfolding of partial applications | 0 | 1.90 | 1445609472 | 0 |
| SourceChordTranspose | 0 | 1.81 | 1444331520 | 0 |
| SourceOpeningResidual | 0 | 2.99 | 1444249600 | 0 |
| TransportedOpening, dependent composed bridge | 0 | 2.61 | 1468203008 | 0 |

Twelve final #print axioms declarations use only subsets of propext,
Classical.choice and Quot.sound. No sorryAx. SourceChordTranspose emits two
unused section-instance warnings, SourceOpeningResidual one unused simp
argument warning; the final bridge has no warnings. The failed initial draft
was not proof evidence. No cap increase, production change, full manifest
replay, or unchanged runtime regression occurred.

## Bounded source scatter/gather adjoint — 2026-09-21

Base `3a53c79a5003755c885fd6b87e98b9d046a9d51d` plus this changeset.
`AspisV8R17/ScatterDual.lean` proves the finite dot-product identity for
the retained scatter edge lists and their gather operation. Input and output
index bounds are explicit. It identifies the gather of sourceEdges with
the weightedIndexLoop read sum, and instantiates the adjoint at any retained
bounded schedule. This uses the existing index certificate, not another
enumeration of dense field matrices.

`AspisV8R17/SourceGatherLoop.lean` models the accumulator in the verifier's
xt: on each set bit it clears the bit, multiplies scale by half, and adds
the weighted read; the final read sets the first clear bit. It proves this
loop equals the weighted read sum. The retained certificates discharge
termination at all inputs below 512 and 513. The double-scatter adjoint
preserves the actual 512 -> 513 -> 514 forward sizes and reverses them for
the gather; the 513 intermediate coordinates are not discarded.

Inspected local tools and identical v19 staged files:

- r17_opening_weights.rs SHA-256
  `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
- r17_coupled_audit.rs SHA-256
  `74f6ec7eff5c747656168dabd1cefd9cb7326fc29c9fd6ccf2d46a10e944c690`.

The opening code pads weights from 1024 to 1028, splits even/odd lanes,
gathers to 513 and then 512, and recombines 1024 weights. The audit's forward
chord computes 1028 coefficients, asserts its high tail zero, then truncates.
The new identities hold for arbitrary inputs at the stated dimensions;
they do NOT assume or establish that high-tail assertion. In particular,
an honest diagnostic assertion is not a malicious-prover image proof.

Next exact proposition: combine these adjoints with the retained
finiteChordEven/finiteChordOdd equations, preserving parity splitting and
zero-extended weights, to prove the entire chord_transpose pairing. Then
compose with TransportDual and the two distinct residual-weight formulas.
Word-level Rust/field refinement, original-weight materialization, extraction,
challenge bounds and the joint privacy obligations remain open. No new hiding
or adjoint assumption was introduced.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; command for each
leaf: `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, timed by `/usr/bin/time -l`.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ScatterDual, initial map-composition simplification | 1 | 10.18 | 1430159360 | 0 |
| ScatterDual, explicit Function.comp_def | 0 | 4.62 | 1444233216 | 0 |
| SourceGatherLoop, loop identities | 0 | 1.72 | 1445806080 | 0 |
| SourceGatherLoop, added double-scatter bridge | 0 | 3.32 | 1447788544 | 0 |

Three ScatterDual and five final SourceGatherLoop #print axioms results use
only subsets of propext, Classical.choice, Quot.sound, with no sorryAx.
The failed draft was not accepted evidence. No production changes, cap
increases, full-manifest replay or unchanged runtime suites were performed.

## Universal inverse-dual algebra — 2026-09-21

Base `7048dd6bb844a46ba49d5f224800720e915da3be` plus this changeset.
New `lean/AspisV8R16/TransportDual.lean` proves `inverseTransport_dot`:
for EVERY coefficient vector c and weight vector w over a commutative ring,
the dot product of w with inverseTransport(c) equals the dot product of the
explicit transported weights with c. There is no honest-generation,
balanced-mask, or legal-witness premise. The forward corollary uses the
retained inverse theorem and pivot membership. This closes the universal
model-level algebraic identity, not its exact-source refinement.

The weight formula subtracts w(pivot) exactly at rows in inactive.erase(pivot),
then permutes by order. This is the predicate `r != PIVOT && inactive[r]`
in the inspected Rust `Transport::dual`. The generic permutation model still
requires source inventory correspondence; the Rust forward/inverse loops
specifically rely on their constructor leaving PIVOT in the final slot.

Inspected identical local tool and v19 staged `r16_basis_transport.rs`:
SHA-256 `36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`.
Inspected staged `r17_opening_weights.rs`:
SHA-256 `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
Its quotient_weights applies this dual to original_weights, then the chord
transpose, then the separate ordinary/structured image residual weights.
The new theorem does NOT prove that chord transpose, original-weight
materialization, residual checks, Rust field operations or extraction.

Focused cached compilation in `/Users/dominic/ZK/AspisFormal`, using
`lake env lean -j1 -M1800 -R <research>/lean -o <r16-cache>/TransportDual.olean
<research>/lean/AspisV8R16/TransportDual.lean`, measured with `/usr/bin/time -l`:

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial sum rewrite | 1 | 8.70 | 1424359424 | 0 |
| Pointwise rewrite; remaining finite-set equality | 1 | 5.18 | 1423835136 | 0 |
| Explicit finite-set extensionality | 0 | 3.19 | 1437286400 | 0 |

Both final #print axioms results contain only propext, Classical.choice,
Quot.sound; no sorryAx. Failed attempts were not accepted proof evidence.
No resource cap increase, production change, unchanged runtime regression,
or full-manifest replay was performed.

First remaining soundness-specific proposition: the exact staged opening
weight pipeline, including chord transpose and distinct channel residuals,
computes the required functional on arbitrary extracted coefficient vectors.
Its Rust/field refinement and subsequent binding, extraction, adaptive
challenge and loss-accounting gates remain open. Joint legal C1/H1/G privacy
coverage remains a separate obligation; this soundness lemma does not close it.

Date: 2026-09-20. Base privacy revision `1d77761f`.

The raw C1 privacy separator is not evidence of a soundness break. However,
R16 changes the encoding/verification relation and must not inherit a
soundness verdict solely because honest fixtures pass.

## What follows from the reversible map

At the algebraic model level, `transportEquiv` supplies both inverses of T.
For any encoder E on the complete message space, `range(E ∘ T) = range(E)`:
one inclusion applies E to Tm, the other chooses `T⁻¹m`. Thus this basis
change does not itself enlarge the ambient codebook or change the set of
codewords on which distance/list bounds are stated. This is a mathematical
consequence, not a compiled end-to-end soundness theorem or a statement
that all such messages satisfy the payment relation.

Original semantic messages and constraints must continue to refer to
`m = T⁻¹c`, where c is the extracted encoded coefficient vector. The
required functional identity is `dot(w,m) = dot(T⁻ᵀw,c)`. It must hold for
arbitrary maliciously supplied c, not merely honestly produced witnesses.
M31/QM31 basis tests and the staged dense differential checks exercise this
identity; its exact-source universal formal refinement remains open.

## Required source gates, none waived

| Gate | Checked evidence | Remaining proposition |
| --- | --- | --- |
| Fixed public transform | Source-derived immutable order; legal-cell assertions; inverse tests; generic Lean equivalence | Concrete Rust loops/field operations refine that equivalence |
| Joint commitment extraction | Both C1 and C2 use the same T; ordinary encoder and Merkle verification retained | Binding/extraction for the new profile yields a coherent c for every batched column |
| Original semantic relation | Ten-round semantic code remains on original rows; honest public-byte verification passes | Accepted point claims equal evaluations of T⁻¹c except for an explicitly bounded bad event |
| Functional transport | Inverse dual precedes chord transpose; dense and entrywise calculations agree in controls | Universal exact-source dual/chord identity and batching bounds |
| Quotient/image condition | Existing top-coefficient checks and verifier image terminal retained | Extracted quotient satisfying new functional checks corresponds to the same encoded polynomial, including all exceptional OOD cases |
| Final values/openings | Existing authenticated openings and structured/dense outcome comparison retained | Full extraction and consistency theorem through all folds and Final256 |
| Fiat–Shamir chronology | Distinct R16 profile absorbed by prover and verifier; exact map included in descriptor | Source oracle transcript, challenge distribution, query budget and soundness loss for this profile |
| Invalid proofs | Both exercised witnesses accept; byte-corruption/truncation controls reject | Quantified malicious-prover soundness, not a finite mutation sample |

The first soundness-specific source theorem is the universal transported
functional identity for the exact verifier weights, composed with the
existing chord transpose and original point/inactive claims. The wider
commitment/extraction and Fiat–Shamir obligations still need their own
premises and loss accounting. The new profile changes transcript bytes;
old challenges or old proof bytes cannot be assumed identical.

There is no current full soundness-preservation claim, no full privacy
claim, and no release/deployment approval. Closing either ledger alone is
insufficient for the user's full-repair goal.

## R17 structured-G integration boundary (2026-09-20)

The R17 prototype would require a G-specific opening functional. The R16
source instead proves one functional of a single gamma-batched message.
`R17_MIXED_MASK_BOUNDARY.md` records source hashes, a compiled impossibility
lemma for unequal functionals on a single combined input, and an executable
negative regression. Changing a common inverse-dual weight cannot repair
that mismatch. A distinct opening argument (such as the specified, still
unimplemented two-channel route) must be soundness-checked; the old verifier
must not be patched to accept unmatched claims. This is not a demonstrated
soundness break in the unchanged protocol.

The next R17 step is now an arithmetic prototype, documented in
`R17_TWO_CHANNEL_OPENING.md`. Its two functionals remain distinct through
both quotient channels, four image residuals and four relation rounds.
The compiled root-count bounds must include the ordinary/carried error:
degree 4 for the combined image check and degree 44 for the combined
query check. The smaller image-only degree-3 bound is not the whole gate's
soundness bound. Uniform challenge, source chronology, binding/extraction
and adversarial query-budget premises remain open; no end-to-end loss or
soundness-preservation claim follows from the prototype.

The subsequent `R17_SOURCE_INTEGRATION.md` records a matched staged host
implementation and honest/negative runtime controls. This advances source
implementation, not the universal extraction/refinement or Fiat--Shamir
soundness gates above. Production protocol paths remain unchanged.
