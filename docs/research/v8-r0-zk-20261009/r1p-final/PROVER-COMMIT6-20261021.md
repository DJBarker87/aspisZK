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
