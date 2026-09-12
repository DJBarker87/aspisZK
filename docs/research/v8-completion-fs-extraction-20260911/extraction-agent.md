# RecoveredHigh, recorded access, and the checked-payment gap

Scoped audit and new executable access prerequisite at source parent
`9e65594156c06b53a2ebea2041a9662850d6bbb8`. No historical Lean target was
recompiled, no large elimination ran, and no claim of full extraction or
Fiat–Shamir soundness is made. All changes owned by this agent are new
`Extraction*` files, this report, and their separately retained results.

## What the checked algebraic event actually says

In `SelectedResidualHighRecovery.lean`, `RecoveredHigh e family gamma kappa
tau alpha` means that **the same** quotient Q has:

1. `Witness`: literal quotient-family membership, no bad ordinary/image
   anchor, equality of the actual post-alpha final to Q's fold, and the
   older `HigherCubicRoot` condition;
2. `HighSupport`: at most 61,336 bad quotient fibres, hence at least 200,808
   good fibres;
3. `SelectedMiddleImageRecovery.Recovered`: there exists p in the fixed
   family with at least 38,228 joint original-symbol matches, the actual
   original(Q) equals gamma-batch(p), and `c1Projection p` belongs to the
   pre-lambda `EarlyC1Family.family c1`.

None of these fields is an algorithm yielding p, a list-decoder execution,
an authorised table read, a payment-residual proof, or a Rust validator
result. The family of cardinality at most one is an analysis construction;
the C1-only family of cardinality at most 100 uses `filterFamily` over the
entire finite message universe. A small output cardinality does not bound
the cost of computing it.

`SelectedResidualRecoveryBound.conditional_nonpair_bound` bounds the ideal
mean of `higherPrefix AND NOT RecoveredHigh`, with its SAME compact suffix.
Outside the SAME product obstruction at the two OOD points, its bound is

```text
117153 / Gamma.card + integratedBudget q Gamma A
  + q / G.card + 18 / A.card.
```

It does not bound `accept AND no checked witness`. The product obstruction,
history-uniform ideal experiment, and later source/FS coupling remain the
separate premises of the existing composition. No new numerical term has
been assigned to the recovered branch here.

The fixed-C1/C2 family and its nonzero E precede the OOD data; the shared
beta depends on the completed OOD prefix and precedes gamma. The witness Q
and final may depend on gamma/kappa/tau/alpha. None is moved earlier by
this audit or by the new access algorithm.

`SuccessfulSelectedVerifierRun.successful_selected_verifier_run_constructs_ideal_execution`
constructs an ideal Execution from its typed `Program` and `SuccessfulAt`.
Its own header excludes complete Rust interpretation, full authentication,
and payment extraction. In particular, its terminal field is the existing
source-shaped scalar equation; it is not a constructor of the payment
witness or a proof of all semantic residuals. Current same-body/source work
belongs to the other agents and is not silently imported as a finished premise.

## Reuse map: do not rebuild an existing resolver or confuse decoders

| Existing implementation/theorem | Exact use and remaining requirement |
| --- | --- |
| V7 `V7MerklePartialPathExtractor.resolvePath` and `V7MerklePrefixTargetCongruence.resolvePath_eq_of_agree_on_log` | Already substantive prefix-local path extraction. No duplicate generic Lean resolver was added. |
| `AuthenticatedEarlyC1Prefix.accepted_opening_prefix_or_late_target_or_collision` | Actual supplied opening agrees with the fixed prefix word, or hits the explicit late target/collision branch. Needs the real recorded prefix and source authentication premises. |
| `authenticated_c1.rs::authenticate` | Exactly fibres 0..255, 256 packed403 C1 values and salts32, canonical checks for all26 columns/four slots, depth18 authentication, then sixteen semantic columns of 1024 evaluations. |
| `authenticated_c1.rs::recover_c1` | Requires that opening bundle and a public `Decoder` whose `first_position=0`; applies the precomputed exact source-basis inverse. It is interpolation, not arbitrary-error correction or minority list decoding. |
| `c1_query_graph.rs::extract_raw`, `candidate_at`, `recover_exact` | Existing source graph controls. The whole-tree extractor materializes 262,144 leaves, recomputes hashes/default inputs, and may reject missing/forward/canonical data. `recover_exact` checks the whole semantic received word; failure of that check is not absence of a valid witness. |
| `GaoC1Recovery.recover_coefficients`, `EarlyC1SampleGame.accepted_coefficient_failure_bound` | Useful conditional circle/Gao mathematics, with actual code/basis/inverse and sample-law interfaces. The latter targets a strong near C1 candidate, not every member at 38,228/1,048,576 agreement. No old artifact was imported into Lean4.33.1. |
| `SelectedEarlyC1PaymentFacts.member_transfer_facts_or_copy_collision` | One same-table amount/input/pair/output-facts composition with one copy-collision alternative. Copy, semantic, positivity, and public-binding residuals are explicit premises; membership supplies none of them by itself. |
| `SelectedMembershipDecode`, `SelectedOutputPair`, `SelectedAppendAfterstate` | Reuse for the actual 1+20+3 input path, output pair and append components; do not substitute old one-output/depth20 spend endpoints. |

The literal `recovered_witness.rs::decode` scans all sixteen C1 columns for
length1024/canonical M31, reads the exact key/note/pair/path/output coordinates,
and validates pair occupancy and Boolean directions. `extract_checked`
first binds the caller's complete runtime context including the **outer**
forest root, then calls the real merged-C1 transfer compiler/validator and
compares the entire returned public transition. Nullifier freshness, context
authority, old snapshot validity and settlement identity are not implied by
polynomial support. Complete same-table source residuals must still be
connected to this literal endpoint, not supplied as `validWitness`.

## Implemented: fixed-window material from recorded answers only

`ExtractionRecordedC1.rs::extract_first_256` takes only:

- one immutable finite list of raw query inputs and their full32-byte
  answers, from the authorised C1 prefix;
- the expected C1 root;
- explicit record, raw-byte and lookup budgets.

There is no hash function argument, oracle callback, extra-opening oracle,
honest tree, encoded column, coefficient vector, mask, or witness argument.
The first input for each truncated208-bit digest is indexed. Repeated raw
inputs must have the same **full** answer; distinct raw inputs with equal
208-bit prefixes are rejected. The adapter follows only the root's left
path to the first256-fibre subtree, then all that subtree's descendants.
Children must have an earlier recorded ordinal than their parent. It does
not create canonical-default preimages or query off-path sibling preimages.

This is stricter than merely allowing every preimage present anywhere in
the prefix. In particular its forward-reference check remains an explicit
access failure; no probability-zero assertion is attached to it.

For success, the structural counts are:

```text
selected subtree: 256 leaves + 255 parents
ancestors above that subtree: 10 parents
total recorded-node lookups: 256 + 255 + 10 = 521
frontier: 10 sibling digests, in source bottom-up order
material bytes: 256*(403+32) + 10*26 = 111620
```

That is the leaf/salt/frontier payload only. `C1Openings` additionally stores
256 explicit `u32` indices (1,024 bytes), plus vector descriptors/capacity and
allocation overhead. Neither number is a proof-body census or measured RSS.

The 521-record positive control stores 125,917 raw-input bytes plus 16,672
full-answer bytes. General index construction scans the entire bounded
prefix, with ordered-map operations and explicit byte accounting; 521 is
the **path lookup** count, not a bound on arbitrary adversary-prefix size.
The result allocates only the fixed opening bundle rather than the full
tree. These are extractor-local data, **not** a new proof transmission.

The returned type is `authenticated_c1::C1Openings`, i.e. the direct input
to existing `recover_c1(root, &material.openings, decoder)`. In this small
control the unchanged source slice through `authenticate` is compiled in
`ExtractionAuthenticatedC1.rs`; `ExtractionCheck.py` checks that slice
byte-for-byte against the historical file before compiling. The selected
field implementation, private-leaf hashing and `v7_merkle208` verification
loop are imported directly from their actual source files. The heavy public
matrix and `recover_c1` solve were deliberately not replayed.

Calling that unchanged authentication slice on the produced bundle returns
the expected **16,384 evaluation scalars**, in slot-major26-column order and
semantic16 projection. Its 256 leaf and 530 parent hash calls are all served
from the same recorded table; an unrecorded request would fail the control.
The access stage itself makes zero oracle calls. Revalidation therefore
requires 786 cached-answer accesses, not 786 fresh answers, when the record
table really is the execution's oracle prefix.

The caller must supply the SAME root read from the proof and the genuine
prefix captured at the actual C1 cut. An arbitrary invented list of answers
is not an authenticated source prefix. The control uses a deliberately
synthetic consistent answer table, not SHA256 or a random-oracle sampler;
it demonstrates the source API/data flow, not cryptographic prefix truth.

## Controls, evidence and reproduction

Run only the new small control:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 \
  docs/research/v8-completion-fs-extraction-20260911/ExtractionCheck.py
```

It compiles with `rustc --edition=2021 -O`, uses the existing aggregate-child
RSS/120s monitoring wrapper, and requires no Cargo dependency build or old
Lean cache. Expected work is one small compilation and fixed521-record
controls, not elimination/proof generation. Both commands passed first try:

| Command | Exit | Measured wall seconds | time peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized compilation | 0 | 1.10 | 187744256 | 0 |
| Control executable | 0 | 0.36 | 5095424 | 0 |

The monitor recorded approximately 1.114s/0.382s including polling overhead
and sampled aggregate peaks 153,760/1,168KiB; sampled values can miss the
process peak, so the time-tool peaks above are retained as well.

Fifteen rejection controls cover insufficient record/byte/lookup budgets,
missing root/leaf, forward edges, wrong leaf/node tags or lengths,
noncanonical M31, full-answer inconsistency, two variants of 208-bit collision,
and appending a missing preimage after its parent. Exact repeated-prefix
records preserve the result. Ten off-path sibling preimages are deliberately
absent in the positive case; their digests are sufficient and authenticated
through the recorded parents.

Evidence is retained at
`results/v8-completion-fs-extraction-20260911/ExtractionEvidence-e6b388z_/`.
It was moved byte-for-byte from the initial docs-local output directory.
The current runner writes subsequent receipts under results; its initial
version is retained as `ExtractionCheck-at-run.py` matching the recorded
hash. No control was rerun just to change the receipt destination.

| Artifact | SHA256 |
| --- | --- |
| `ExtractionRecordedC1.rs` | `3231b34aabc213a42d280048f95a162a4859ec0667216b972bb44d0397d4c363` |
| `ExtractionAuthenticatedC1.rs` | `85ada1204090551307c2144a69a5304ba74cf66a21aa40b61ce6c969f1550f19` |
| `ExtractionRecordedC1Control.rs` | `9a4d6ca4120e4a970d0d4b612ba42b2bf333e5ad49d7cf998315fdefa7fb30fc` |
| Current `ExtractionCheck.py` | `4a8f1cd289dab0e3a3d295fb6ee46ffb2211f809beaf6d4786c6470e95e4e2d0` |
| Run-version wrapper snapshot | `15809b04af661a2ea066abb1cbd387e2fb60351cb84dc1496cf8a3ad057566d7` |
| `ExtractionReport.json` | `74669f80107abf8a17906d649ebaa40829b2cbdf3c24637332089d3de4154311` |
| Compilation log | `0b87f401bcb863619c5680e5565e8cb55e57bf7927fec6f08354d8236c55b0f9` |
| Control log | `af56976d6616507d853f0df14f2772de0312658da06235cd616587d06dc3c788` |
| Executed binary, identical hashes before/after execution | `17e919ba9de31d182cd31bc0661908bf117b4760aa4bbe7dd783fecb3475a3a1` |

The temporary binary was deleted normally after hashing. No new Lean proof
or axiom audit is claimed for this Rust experiment. It is not independent
verification of the old4.32 proofs; compatible V7 source interfaces were
reused without transplanting their cached compiled outputs.

## Exact residual event still required

Let A be successful actual selected verification, R the corresponding
`RecoveredHigh` event, H the corresponding `higherPrefix`, and X success of
one **specified resource-bounded, allowed-access extractor** returning any
witness accepted by the actual context/transition validator. Under a correct
source-to-ideal correspondence, the higher-branch extraction failure splits
disjointly as

```text
A AND H AND NOT X
 = (A AND H AND NOT R AND NOT X)
   OR (A AND H AND R AND NOT X).
```

The existing residual bound addresses the first term, not the second. Within
the second, let M mean success of this exact fixed-window access adapter,
and let V mean that some member of the fixed mathematical family has a
canonical semantic table whose **literal** `extract_checked` succeeds for
the same independently authenticated public/context/transition data. Then
the still-open recovered term has this useful disjoint precedence:

```text
delta_access = Pr[A AND H AND R AND NOT X AND NOT M]
delta_semantic = Pr[A AND H AND R AND NOT X AND M AND NOT V]
delta_enumeration = Pr[A AND H AND R AND NOT X AND M AND V].
```

The H conjunct is retained without assuming or needing a separate R⇒H bridge.

All are joint events over the original execution, not conditional success
ratios. Incorrect/missing prefix-source provenance belongs to the separately
charged source/authentication boundary before applying this decomposition.
The term `NOT X` is retained everywhere: extracting any valid witness counts
as success, including one outside this analysis family.

No bound for these deltas is supplied by this experiment. A q22 proof has
only 88 original evaluations per column and does not itself provide the
fixed 256-fibre opening window. More importantly, even when this window is
available, `recover_c1` may interpolate a table different from a valid
minority family member. The existing outside-window/changed-window and
near-only controls already forbid promoting ordinary interpolation to a
complete low-agreement list decoder. Repeating it is not the missing proof.

The decisive remaining obligations are (i) actual prefix/accepted-event
access or a rigorously budgeted alternative sample/rewind producer, (ii)
efficient candidate generation covering the relevant low-agreement member,
and (iii) same-table semantic/copy/public/settlement derivation implying
literal checked-payment success. This work closes the concrete fixed-window
material-production API only; it does not assert that these remaining
events vanish or that global soundness/FS extraction is finished.
