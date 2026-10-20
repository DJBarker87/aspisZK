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
