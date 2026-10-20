# Prover commitment continuation 6 — 2026-10-21

Branch `codex/cx-prover-commit6-20261021`, base `2086caeff`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit6-20261021/`.

## Stage 1: quotient law

`ProverCommitQuotientLaw.mp_completeOrSpare` proves the new middle-tape
law: decode the H1 quotient; on success keep its visible coordinates and
use the independent spare tape's padding; on failure use the spare tape.
This is measure preserving on full tapes. No sampler words are consumed
for completion. Full equal successful fibres imply quotient equal fibres
with constant `card(Padding) * cF`, via an explicit fibre equivalence.
`ProverCommitQuotientStrict.quotient_law_strict` gives a strictness witness:
every deterministic quotient section has quotient fibre size one and
fails every full-tape equal-fibre law.

Accepted env J attempts: 8191 (law, exit 0, 1.80 s, 3,530,900 KiB peak RSS)
and 8193 (strictness, exit 0, 1.60 s, 3,519,504 KiB). Zero swaps; all five
audits use only propext, Classical.choice and Quot.sound. Drafts 8188–8190
failed elaboration and are excluded. Host scopes use MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. A private copy of
the existing joint launcher changes only TasksMax; its existing MX argument
sets the requested memory limits. Global launcher and peer sources stay
unchanged. Exact source hashes, dependency fingerprints, base revision,
commands, outputs and timings accompany each receipt.

Further stages and the final signature/checklist diff follow below.

## Stage 2: release endpoint unchanged after quotient transport

`PrivacyR1FinalProtocolQuotient.privacy_R1_protocol_quotient` has the exact
same conclusion as `PrivacyR1FinalProtocolHistoryReal.privacy_R1_protocol_history_real`:
the same source experiment, simulator, numerical error and strict 2^-100
bound. Its only premise change replaces full-tape successful fibres with
successful fibres of `Option.map project ∘ tapeOf`. The constant `cF` now
counts quotient fibres. No observable-invariance premise is added.

The internal coupling retains its original real map, full answer vectors,
exhaustion events, collision events, read indices and budgets. Only its
middle map uses `completeOrSpare`. `completed_view` and `middle_completion`
prove equality of the entire retrying middle test, including payloads;
`cpQ` has uniform full-tape marginals and `realModel_quotient` reuses the
existing agreement/freshness/exhaustion proof. Completion draws no source
words and creates no new retry failure. This is a quotient replacement of
the actual protocol endpoint, not just a standalone honest-view statement.

Accepted J 8194/8195/8196/8197: coupling/model/privacy/release endpoint,
exit 0, respectively 1.88/1.77/1.69/7.79 seconds, peak
3,542,964/3,542,620/3,538,228/4,092,560 KiB; zero swaps. Ten audits use
only standard axioms. J 8192 is an excluded elaboration draft. No existing
endpoint, source-identification, runtime-join or peer-owned module is edited.

Signature diff (all other binders and the conclusion are byte-identical):

```diff
-(R_commit_equal_fibres : ∀ τ : Tape K F, ... tapeOf e.1 e.2 = some τ ... = cF)
+(R_commit_quotient_fibres : ∀ τ : SourceTape K F,
+  ... quotientDecode (fun e => ...tapeOf e.1 e.2) e = some τ ... = cF)
```

`full_fibres_imply_quotient` converts every old instance to the new premise
at `card(Padding) * cF`; `quotient_law_strict` proves the converse false.
The probability conclusion does not mention cF, so it changes neither the
error nor the experiment.

## Stage 3: commitment observable and field carriers

`ProverCommitQuotientObservable` proves invariance of every selected leaf
encoder and the entire commitment-address function of the actual constructed
protocol instance. `protocol_observable_mass` transports the joint law of
the full honest view and all commitment addresses, including unopened
leaves, all tree positions, salts/bindings/seeds and expander addresses.
It requires no new invariance hypothesis. The previous continuation's
warning about arbitrary residual `leafVal`/`caddr` does not apply to the
constructed `PhaseProtocolInstanceBin.prover`: those fields are overridden.
This closes the commitment-observable transport sub-obligation, while
identifying the shipped caller with that instance remains separate.

`ProverCommitWordCarrier` selects the actual M31 image subfield as
`(algebraMap (ZMod P) K).fieldRange`; `baseEquiv` is lossless. Rejection of
the exact low-31-bit candidate agrees with `rejB`. Every accepted field
value has exactly two 32-bit preimages, proved by an explicit two-element
set, without enumeration.

`ProverCommitSourceCarrier` constructs an explicit equivalence between the
five **pre-balance** sample families (eligible noise, ten mask-only columns,
G, inactive nonzero-row H1 and D) and `SourceTape`. Its `source_fibre_card`
transports every individual successful fibre exactly. There is no assumed
common fibre constant. The carrier deliberately retains the sampled values
subsequently overwritten by balance in mask-only/G/D. Feeding the shipped
post-balance material directly into this carrier would not recover those
raw samples. They must be recovered from the actual consumed stream.

Accepted J 8202/8205/8208: observable/word/source-carrier, exit 0,
3.00/2.22/2.00 seconds, peak 4,062,896/4,041,536/3,529,980 KiB; zero swaps.
All twelve audits use standard axioms only. Rejected local elaboration
drafts are retained and excluded. These laws do not yet identify the Rust
caller order or assert uniform successful fibres for the sequential stream.

## Stage 4: sequential decoder law and model budget instance

`ProverCommitSequentialFibres.sequential_equal_fibres` proves a generic
consuming rejection decoder's equal fibres by induction on available words.
One rejected head contributes `c₀` copies of the same target fibre with one
fewer try; an accepted head contributes `c₁` copies of the tail target with
16 fresh tries. Zero remaining limbs accept without inspecting the suffix.
For M31, `c₀ = c₁ = 2`. The common fibre constant is a named symbolic
recurrence; no large numeral or tape is evaluated. An early specialized
proof exposed elaboration/finite-instance comparison issues. The replacement
isolates the generic alphabet theorem and uses explicit finite-set transport;
all failed drafts 8209–8221 are excluded, not release results.

`ProverCommitSequentialArrays` transports that theorem to indexed arrays
and two independent streams. `ProverCommitSourceDecoder` supplies the
explicit quotient decoder on the **existing two block-answer carriers**:
`inputEquiv = wordsE E₁ × wordsE E₂`, the exact M31 image field, the four
stream-1 sample families, and the full 4096-limb D stream. Its
`quotient_equal_fibres` derives `quotientFibreSize`, with **no assumed cF**.
The index bijections are explicit mathematical enumerations. Matching them
(up to a coordinate bijection) to the shipped caller is not inferred.

`ProverCommitSourceCounts.source_counts/source_budgets` supplies a universal
**coordinate-model** RCommitCount instance, both stream inequalities, both
block upper bounds and both counter bounds. Eligible cells inject into
16×1024 and free H1 rows inject into 1024; no registry enumeration is used.
The actual source caller/read-completeness instance is still separate.
`ProverCommitSourceFailure.quotient_failure` proves that packing adds no
failures: exactly one of the two sequential array decoders must fail.
This theorem does not equate their failures with `CommitReadsR1.Exhausted`.
`ProverCommitSourceSuccess.decoder_has_success` gives a symbolic all-accepted
word input, so the fibre law is not an all-failure construction.

Accepted J 8222/8224/8229/8232/8235/8236: exit 0, respectively
2.52/2.09/2.39/6.65/1.78/2.49 s; peak
4,055,380/4,041,124/4,115,408/4,215,704/4,023,528/4,172,692 KiB;
zero swaps, standard axioms only. No Rust, Aeneas or SBF job is run.

## Demonstrated source obstruction and exact remaining equation

`source-frontier.json` checks all four aggregate caller/balancing function
bodies against the retained failed source extraction: they are unchanged.
Both current Charon and Aeneas binaries also match the old pinned hashes.
The original aggregate LLBC had iterator clause errors (`Enumerate` and
`IterMut`); the original Aeneas replay exits 2 at the G loop
(`InterpAbs.ml:191`). The carried variants retain their separate failed
receipts, including the D-loop internal error and the clean-reference
`Not_found`. None is a source certificate. The unchanged failing aggregate
is not replayed. Single-try Kani and the proved sixteen-step scalar
composition do not certify the unlowered aggregate callers.

The precise next source obligation is an equation on **every** pair of
actual block-answer vectors: project the successful shipped caller's raw
pre-balance sample tape, and obtain the sequential `quotientDecoder`, with
the M31 image field and source coordinate/cell bijections. Source material
alone has already discarded dependent samples; reconstruction must use the
consumed raw words. `quotient_premise_of_caller` states and checks the
exact transfer once that equation exists. The equation is not installed as
an axiom or silently discharged by the mathematical decoder.

Still required independently: the exact source cursor/`wordsE` failure
classification supplying RExh, and complete source read-log coverage for
all tree/seed/salt/binding/expander calls. This is the demonstrated stopping
frontier for the universal source caller/count/exhaustion instance. The new
coordinate-model budget theorem is not advertised as that source instance.
Consequently no **complete source checklist row** is marked discharged.

`ProverCommitSourceCallerLaw.source_representative_not_full_fibres` also
checks strictness on the **same two byte-block input carriers** used by the
protocol. The nonvacuous sequential decoder followed by a deterministic
zero-padding section satisfies the quotient law (by
`representative_quotient` and `quotient_premise_of_caller`) and fails every
full-tape equal-fibre law. Accepted J 8238: exit 0, 1.98 s,
4,032,864 KiB peak RSS, zero swaps; all three audits standard.

## Exact signature diff

The full signatures are retained verbatim in `signature-before.txt` and
`signature-after.txt`. `harness/signature.py` verifies the conclusion and
all other binders byte-identical. The generated diff is:

```diff
--- PrivacyR1FinalProtocolHistoryReal
+++ PrivacyR1FinalProtocolQuotient
@@ -1,12 +1,12 @@
-theorem privacy_R1_protocol_history_real
+theorem privacy_R1_protocol_quotient
     (seed : R1ProverP K CommitHandle Aux F
       (wire base ((base.pubBytes x).length) h B outputs x).toWire)
     (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
     (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
     (cF : ℕ)
-    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
+    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
       (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
-        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
+        quotientDecode (fun e => ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2) e = some τ)).card = cF)
     (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
     (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
     (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
```

## Before (verbatim)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
```

## After (verbatim; nine complete source rows remain open)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input; the actual source/caller/order/field-image equation remains open. |
| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Quotient packing adds no failures; the source caller/cursor law and exact wordsE-to-Exhausted classification remain open. |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |
```

## Final release evidence and ELF rule

One final coherent new-cone audit, `R1Z.ProverCommit6Audit`, env J **8239**:
exit **0**, wall **1.74 s**, peak RSS **4,038,252 KiB**, **zero swaps**.
Source revision **d8f573e17** contains every adopted source byte; the audit
was compiled from the same SHA before its source-only commit. The exact
source SHA256, dependency fingerprint, host source/object hashes and all
52 verbatim `#print axioms` results are retained in `lean/`,
`source-release.json`, `final-host-hashes.json` and `final-audit.json`.
Every axiom set is a subset of `[propext, Classical.choice, Quot.sound]`.
All 17 release modules match accepted focused receipts and the final own
object dependencies; `harness/validate.py` passes without rerunning a
compiler/solver. Failed drafts remain excluded and their exact source text
is retained under `lean/sources/`. Two dependency preflights (before actual
8211 and 8232) launched no compiler and consumed no attempt; both numbers
were subsequently used normally. Attempts **8188–8239** are consumed;
next available is **8240**.

The final scope uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, Lean -M7000, and the existing shared reservation/slot locks.
No global launcher or peer-owned source/object is replaced. Only own new
modules are installed; any previous own draft/source/object is snapshotted.
The existing frozen manifest is not replayed unchanged; all changed targets
were checked in order and the complete additive cone imported in the final
audit. No generated certificate, arithmetic gate or cold dependency build
runs.

No crate, program, Cargo input or shipped function changed in this
continuation. All **491** hashes in the retained accepted ELF source
inventory match. `elf-inheritance.json` records the inherited three
byte-identical `cmp` verdicts, artifact SHA256s/sizes and accepted build
receipts. The unchanged SBF/runtime/adversarial gates are not repeated.
No binaries or objects are committed. No keys are created, read, unlinked
or deleted; no deployment, transaction, merge or push occurs.

The task stops at the demonstrated aggregate source-lowering obstruction,
with the source caller identity, exact RExh cursor classification and
universal source read completeness still open. The quotient release endpoint,
strict weakening, complete constructed commitment-observable transport,
sequential model decoder/fibre law and model count/budget instance are
checked results, rather than proposed replacements for those missing source
identifications. SourceIdentification, RustRuntimeJoin and
PrivacyR1FinalRelease are untouched.
