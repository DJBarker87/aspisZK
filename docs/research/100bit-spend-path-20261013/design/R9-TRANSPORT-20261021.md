# R9: abstract two-transaction experiment and transport (2026-10-21)

Branch `codex/cx-r9-transport-20261021`, base `6302ea9d3`.
Paths below are relative to `docs/research/100bit-spend-path-20261013/`.
This additive model packet does not instantiate the frozen source or close R9.
Existing Lean modules, verifier/prover source, shared objects and keys are untouched.

The model transport reduces C3's supplied probability inequality to pointwise
source execution facts. The preferred soundness interface is
`OrderedSourceRefinement` plus `ScanRejects`: off exhaustion the designated
source recording equals C3's recording, and exhaustion cannot accept. This
gives a stronger zero-scan-charge inequality and therefore C3's existing
interface. An alternative equal-fibre word correspondence derives the stated
additive QueryScan charge. Both compose with M9-binary; neither instantiates
the frozen runtime/source experiment or closes the listed source gap rows.

## Stage 1: experiment and pointwise coupling

`lean/R9TwoTransactionExperiment.lean` defines a finite causal byte-oracle
program: run stage 1, retain its checkpoint and completed query tape, reject
if there is no checkpoint, otherwise run stage 2 with that exact checkpoint.
`eval_success` proves chronological concatenation of the two interpreter
traces. Both stages use one total byte oracle in `eval`, and one memo table
in `lazyMean`; there is no intertransaction reset.

The continuation returns a designated recorded view: its public statement,
messages, acceptance flag and the log consumed by the existing recorded
extractor. This is an abstract source observation/projection, not an invented
implementation of the frozen decoder or writer. Full source interpreter
calls can exceed that designated core log. The source refinement must prove
the projection correct for the actual experiment, including its same public
Rspend; arbitrary supplied recorded values do not establish this.

`failure` is successful continuation acceptance with extraction returning
`none`, for the same recorded view and independent private extractor coins.
`deployedMass` averages those coins. Source failure probability will average
this observation over the lazy source program. Rejection is retained rather
than conditioned away. The query tape is completed even on rejection;
unexecuted suffix draws are ghost padding whose source correspondence is owed.

`joint_inventory` consumes the exact common-carrier consistency and coverage
certificates supplied by LOG-TX2's separately compiled tx1/tx2 results.
It applies `RawDigestLogCarrier.append_consistent` and `append_covers`.
This avoids the known generated-package global-instance import collision.
It proves a consistent covering union, not chronological ordering. Chronology
comes from `experiment` and still requires actual-source correspondence.

`OrderedSourceRefinement` states a pointwise source-run equality off query
exhaustion. It preserves the complete designated log, exact public/messages
and acceptance, and therefore works for every extractor coin tape.
`pointwise_transfer` applies the existing QueryScan finite transfer theorem
for those tapes. It derives the failure inequality; no mass inequality is
assumed. The source law remains stronger than the current R10 inventories.

## Validation so far

Focused stage-1 compile: `R9TwoTransactionExperiment`, attempt 2, exit 0,
11.104 s, peak RSS 3,584,671,744 bytes, zero swaps, three standard-only axiom
audits. Attempt 1's ambiguous `State` namespace and consequent elaboration
errors are retained as failed evidence. No memory failure or cap increase.
Full commands, source snapshots, dependency hashes, revision, timing and
audits are under `evidence/r9-transport-20261021/manifest.json`.

## Stage 2: finite-source probability transport

`lean/R9QueryScanTransport.lean` defines `Tables source` as the answer tables
on the source program's finite potential support, including all branches.
`QueryWordCorrespondence source Residual` contains an explicit equivalence
between these tables and `(Fin 64 → Fin (2^18)) × Residual`, and a pointwise
equality identifying its first coordinate with the source's completed tape.
Residual is finite and nonempty. This is an exact equal-fibre requirement,
not an assumed failure probability, not fresh coins substituted for ROM
answers, and not something implied by R10's backend consistency.

`word_failure_mean` identifies the uniform tape event mean with the existing
`QueryScanModelFailure.failureProbability`. It is proved for symbolic N;
no concrete function-space enumeration or cardinal normalization is used.
`abort_mass` transports the equal-fibre correspondence through the existing
finite-support lazy-oracle law, `mean_equiv` and `mean_prod`.
`transport` puts source and model on the union of their potential supports,
applies the proved pointwise transfer, and derives exactly

```
lazyMean source emptyTable deployedMass
  ≤ lazyMean model emptyTable failureMass
    + QueryScanModelFailure.failureProbability (2^18).
```

The equal-fibre law is deliberately explicit. For example, a source returning
all-zero words certainly exhausts; a mere shared-hash/consistent-log premise
cannot certify the uniform model probability for it. The source work must
account for eight byte blocks, masking/word order, previously queried or
repeated addresses, adversary history and ghost completion. If unconditional
uniform completion is unavailable, this interface cannot be instantiated as
written. One must instead prove acceptance-preserving refinement without a
scan charge, or extend the coupling with separately justified bad events and
charge them. This packet does not assume such extra events have zero mass.

Stage-2 focused validation: `R9QueryScanTransport`, attempt 5, exit 0,
4.874 s, peak RSS 3,548,905,472 bytes, zero swaps, three standard-only audits.
Failed drafts are retained: namespace omissions, concrete cardinal reduction,
empty-table rewrite transparency, and higher-order matching in `mean_prod`.
An intermediate draft reached the default heartbeat limit while unfolding
concrete `fails` during equivalence matching; making that event locally
irreducible and supplying explicit arguments replaced that proof search.
No limit was raised. Attempt 4's compiler diagnostic was retained, but the
runner then failed to remove a shared lock directory which had become
nonempty. No foreign lock files were deleted. Its receipt is reconstructed
from its original command/source/log and rounded `/usr/bin/time` wall field,
explicitly marked as such. Later receipts preserve lock-cleanup errors rather
than losing compilation evidence. This was a failed target, never a rerun of
an unchanged passing source.

## Exact narrowing of C3 and remaining gap rows

C3's old `h_R9_transport` supplied an inequality for a free rational
`deployedFailure`. `lean/R9C3Transport.lean` defines that rational as the lazy
mean of `experiment tx1 tx2`'s `deployedMass`. `c3_transport` proves the exact
`R1FinalSoundness.DeployedTransport` type. `c3_transport_obligation` preserves
C3's `BoundaryEvidence s → ...` quantifier without modifying C3.

| New contract / parameter | Exact requirement | Gap rows still carrying the source work |
| --- | --- | --- |
| Abstract tx1/tx2 and `First.checkpoint` | Source interpreter refines admitted stage 1, authenticated checkpoint persistence, Pool/nested stage 2, and rejection on all branches; ghost padding preserves outcomes. The passed checkpoint is literally the stage-1 result. | R9/R15/R16/R20; P2/P2′ provenance and same public statement; R21/R22 and candidate re-pins for the chosen freeze. |
| `OrderedSourceRefinement` | For every H off the scan event, each resumed designated source RunView equals `eval H (recorded D d P)`. Equality includes ordered core log, public, messages and verdict, before averaging extractor coins. | R9/R10/R16/R20; complete source call coverage and order, source/backend correspondence, both-variant same-Rspend and reachability. This is not discharged by a checklist Prop or an inventory set. |
| R10 `actual1`, `backend`, `tx2Certificate`, `coverage1/2` in `R9SourceLogHandoff.embedding` | Exactly LOG-TX2's conditional one-log embedding inputs. The tx1 actualness and tx2 certificate come from their separately checked call/backend theorems; coverage quantifies every reached call. | R10/R19 plus R-wire; whole callers, rejected prefixes, runtime/backend reads and chronological projection remain. |
| `QueryWordCorrespondence` | Explicit finite-table equivalence with a uniform 64-word coordinate and finite nonempty residual; source tape equals that coordinate pointwise. | R4/R9/R10/R19; source scan/array-driver order and byte masks, fresh-word/history accounting, oracle/backend transport and padding. This is stronger than mere digest consistency. |
| Existing M9-binary `hQ`, `htag`, `hchecks`, `hknown`, `hN` | Original reads ≤Q+1161, public tag 2, universal terminal Checks, exact known-public LiteralCompletion, and recognized starts ≤33. | Existing C3 R18/R19/terminal source obligations and R-wire/M7 decoder completion. They are unchanged by R9 transport. |

The first two rows are an abstract source-execution refinement contract, not
a complete Solana semantics. In particular complete call coverage + ordering
+ backend digest consistency alone do **not** prove same-statement acceptance
or uniform scan words. Those facts remain explicitly in the pointwise
contracts above. No runtime/compiler correctness is inferred from a trait
signature, checkpoint checksum or equal digest. No new trust axiom, supplied
failure bound, assumed final numeric inequality or postselection law enters.

`source_binary_failure_bound` applies
`BinM9C3Closure.composed_binary_failure_bound_known_public` using the derived
transport. The existing binary M9 and numeric endpoint then give the same
per-attempt `6(Q+1161)^2/2^256 + 33·B + 2^-126 + 2^-454`, and `<2^-100`
for Q≤22482956455467539568187. Bank and query-scan charges each appear once;
there is no change to the historical extractor/decoder words or grinding
budget. Binary completion is not discharged. `rejected_stage1` checks that a
missing checkpoint cannot contribute to the accepted-failure event.

The independent R10 handoff directly invokes
`RawTx1Tx2ConsistentLog.cross_transaction_assembly`, rather than reasserting
its conclusion. Its stage-2 certificate is the common carrier output of
`RawTx2DigestLog.log_consistent`; stage-2 coverage is supplied by
`RawTx2DigestLog.every_reached_call`, with its completeness input. The two
generated extraction environments remain separate as required by LOG-TX2.
The model probability proof does not consume raw inventories as if they were
chronological executions: converting them into the designated execution log
is exactly part of `OrderedSourceRefinement`.

## Preferred soundness route: scan errors reject

`lean/R9RejectingScanTransport.lean` provides a stronger alternative to the
uniform-word route. `ScanRejects source` states pointwise that exhaustion
cannot reach an accepting resumed RunView. This is the source error-propagation
fact described in QUERYSCAN (and still requires concrete scanner/caller
correspondence). Together with off-exhaustion `OrderedSourceRefinement`, it
gives `AcceptedSourceRefinement`: every accepted source recording equals the
model recording under the same H.

`transport_no_scan_charge` then proves deployed failure ≤ model failure,
without any fresh-word, probability, residual-equivalence or query-budget
hypothesis. Its C3 wrapper adds the nonnegative model scan probability only
to match the existing `DeployedTransport` interface. The corresponding
`source_binary_failure_bound` composes M9-binary with precisely two R9 source
facts: ordered same-statement recording off exhaustion, and rejection on
exhaustion. Existing M9 source/decoder/budget inputs are unchanged.

This is the preferred R9 soundness narrowing for the actual verifier: the
additive QueryScan coupling route is available when an equal-fibre word law
has independently been established, but unconditional scan uniformity is
unnecessary when source exhaustion rejects. R4/R9 still owe the production
scan/iterator correspondence and error propagation; the program parameter is
not silently identified with the frozen caller. No scan or compiler semantics
has been extracted anew in this task.

## Final focused verification and release boundary

All five final targets compile with Lean 4.32.0, `-j1 -M4400
-DElab.async=false`, `/usr/bin/time -l`, the shared mkdir lock and private
`/tmp/codex-cx-r9-transport-20261021-objects`. All 17 theorem audits are
subsets of `{propext, Classical.choice, Quot.sound}`. Zero swaps throughout;
no memory-limit failure or cap increase, and no unchanged passing target was
rerun. Lock waits are excluded from compiler wall time.

| Target | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Theorem audits |
| --- | --- | --- | --- | --- | --- | --- |
| R9TwoTransactionExperiment | 2 | 0 | 11.104 | 3584671744 | 0 | 3 |
| R9QueryScanTransport | 5 | 0 | 4.874 | 3548905472 | 0 | 3 |
| R9C3Transport | 2 | 0 | 13.121 | 3613212672 | 0 | 4 |
| R9SourceLogHandoff | 5 | 0 | 10.016 | 3464314880 | 0 | 1 |
| R9RejectingScanTransport | 1 | 0 | 7.423 | 3612278784 | 0 | 6 |

Every attempt has its exact command, source snapshot/SHA, revision, direct
import hashes, search path, exit, wall, peak RSS, swap count and multiline
axiom report in `evidence/r9-transport-20261021/manifest.json` and individual
receipts. Attempt QueryScanTransport-4 has the marked reconstruction described
above. Failed logs contain Lean's error-recovery `sorryAx`; no accepted audit
does. C3Transport-1 failed only on ambiguous definition names in its rejection
proof; qualifying those names supplied the replacement.

R10 handoff attempts 1–3 exposed partial cache namespace selection (missing
PublicPreparation.Funs, MaskD2Glue and R572SequentialWordMass). A private
coalesced namespace experiment, recorded by hash/size in
`r10-namespace-objects.json`, then exposed a genuine declaration collision:
`R1SemanticHit` already contains `R0P.Mask.decisionZ.congr_simp` from
`R0P.MaskD2Glue` when loaded together with the R10 environment. That combined
import item was stopped. The replacement removes the unnecessary import of
the extractor-mass environment from the independent R10 handoff and uses
LOG-TX2's exact retained search path. Attempt 5 succeeds. Its result speaks
the common log carrier consumed separately by the model module. No shared
object/source was overwritten. The private coalesced experiment was not
used for a passing result; its manifest is failed-path provenance only.

The local runner now fingerprints search-path changes as well as direct
imports, and refuses unchanged source/import/path attempts. Namespace repairs
were environment changes, never unchanged reruns of memory failures. The
remaining combined-environment/coherent-release import issue is explicitly
not solved by these focused standard-axiom checks.

Read-only final audit:

```
python3 evidence/r9-transport-20261021/audit.py
```

It checks current source hashes against accepted snapshots/receipts, every
new theorem's axiom-audit coverage, standard-only accepted axioms, direct
import hashes, zero swaps, and that all changes from base `6302ea9d3` are
additive and confined to this packet. `audit.json` records its result.

No frozen-manifest replay, extraction, Rust/SBF/runtime/reproducible-build
suite, deployment or push was run. Those sources/artifacts did not change;
this is a model/interface proof packet, not C2 release evidence. Source
instantiation, complete chronological coverage, writer/account provenance,
Pool/both-variant same-statement reachability, scanner/error propagation,
backend/runtime/compiler correspondence, decoder completion and coherent
release integration remain open under the exact rows above. No wallet,
account key, rent, authority or funds were touched. No binary, object,
archive or symlink to an object is committed.
