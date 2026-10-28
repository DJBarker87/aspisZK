# Privacy premise ledger — 26 October 2026

**Target not yet established. No premise is discharged by this audit.**

| Scope (syntactic families) | T | P | C | stream B | external |
|---|---:|---:|---:|---:|---:|
| All syntactic rows | 26 | 369 | 4 | 373 | 26 |
| Data/guard fields (not proof gates) | 0 | 42 | 0 | 42 | 0 |
| Already proved canonical/internal families | 0 | 87 | 0 | 87 | 0 |
| Carried honest-domain guards | 0 | 22 | 0 | 22 | 0 |
| Explicit native-cut overlaps | 0 | 57 | 0 | 57 | 0 |
| Remaining obligation/trust/vacuity families | 26 | 161 | 4 | 165 | 26 |

**Highest-fan-out blocker: `RustRealRefinement`’s concrete deployed `RunJoin.agreement` (V038).** It requires the actual complete view and observer decision to equal the model outside the fixed bad event. Remaining callbacks, body/prefix equations, native effects and trace interpretation feed this join; marginal uniformity alone cannot supply it. This is dependency fan-out, not an asserted numerical count or a new impossibility result. Its two marginal laws (V036–V037) must use the SAME coupling.

Snapshot and evidence: `evidence/privacy-ledger-20261026/input-pins.json`.
This ledger audits `R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its deployment boundary. T = accepted external trust; P = must be proved/instantiated; C = contradictory or vacuity-suspect. Owners are stream B or external. A packaged structure never discharges its fields. Quantified families remain families; conjunction leaves split while witnesses and guards remain shared. Data fields and already-proved internal consequences are labelled separately from open gates. Nothing here closes an obligation.

## Mechanical statement and hidden dependency inventory

Successful mechanical captures: [full readable signature and direct fields](../evidence/privacy-ledger-20261026/readable-20002.log), [nested fields](../evidence/privacy-ledger-20261026/fields-20004.log), [internal consumer hypotheses](../evidence/privacy-ledger-20261026/consumers-20005.log). Each helper has `pp.all false`, `#check @...` or `#print`, and no declarations of proofs/theorems. The literal explicit-binder source block, including its local notations and all three conclusion conjuncts, is retained in [endpoint-explicit-binders.lean.txt](../evidence/privacy-ledger-20261026/endpoint-explicit-binders.lean.txt). The initial maximally explicit diagnostic (20001) is retained, but its expanded typeclass terms hit pretty-printer ellipses; 20002 is the readable statement of record.

The complete binder order is `{CommitHandle Aux}`, `template`, `outputs`, `x`, `rust`, `[Fintype rust.RealRand]`, `[Nonempty rust.RealRand]`, `observer_program`, `refinement`. The first conclusion is guarded by `∀ adv w, public w=x.1`; the other two are numerical inequalities. There is no runtime IdealRand Fintype/Nonempty premise: the comparison is against the mathematical `simE` through the reencoded source, not a claimed deployed simulator. The numerical term is `modelError + 16/2^486 + freshBudget(8*n1+1) + 2*seedBudget(2^64) + 2*fuelCharge`, with the same expression proved <2^-100. This numerical theorem does not prove the refinement.

`RustRealRefinement` is `∀ adv w, public w=x.1 → Nonempty RunJoin`. Unpack its ONE witness into cp.S/finS/nonemptyS/toR/toM/meanR/meanM and agreement. The model side of toM is `((source.RealRand × OracleAnswer) × Tape)`; Tape has24 independent five-word coordinates. `bad` is the existing real parser-bad event OR the global seed-prefix guess at i=0 OR the global five-zero-draw failure at i=0. No independently selectable bad predicate or omitted rejected suffix is authorized. `realSeedQueries` runs the supplied adversary program on the first good output/log or on failView/empty log when all fail. `observerMap` keeps the SAME complete Boolean decision, not a weaker observer.

The proof explicitly calls `Admitted.FixedObserver.privacy_headline_admitted`, `Admitted.builder_premises`, `caller_law`, `budgets`, `fibres`, `exhaustion`, `core_privacy`, `batches`, `ordered_log`, `test_bound` and reencoding transport. Their declarations/bodies are printed; the nested fields are counted below. **The namespace `Admitted` is not a Lean admission:** the fixed observer theorem calls proved self-joins; builder_premises is derived for BuilderSource.prover; caller_law constructs the fixed operational-reference decoder law. Their hidden model facts are listed, not reclassified as open native proofs or external trust. The separate `BuilderRefinement.Admitted` really is a three-field input structure: publicCorr, words, semantic; all nested law leaves are inventoried. `ModelRel.pubBase` aliases the same nine PublicBase rows, and BuilderSoundOn introduces the same guarded witness domain, not an independent arbitrary witness.

The ledger uses quantified law families, not scalar cells. Conjunction leaves split, while all existential witnesses, typeclass instances, guards, and the common coupling remain SHARED. An iff is split only where the E2 atomic contract exposes its two directional guarantees; disjunctions remain event/alternative laws. Payload equalities stay whole. Carrier well-formedness is shown as data, not an additional security assumption. P labels data requiring deployment association as well as implementation/model laws; status distinguishes these. There are no percentages of completion and no assertion that all rows are independent. The original reference ledger and its helper sources were read in-tree under `evidence/premise-ledger-20261025/`; the requested old `docs/.../evidence/...` git-log path has no matching history in this checkout (retained search output).

**Non-vacuity:** rust.RealRand is explicitly nonempty. rust.Adversary need not be; the matching witness/public fibre may also be empty. The theorem universally quantifies a free rust and does not provide a deployed FSExperiments instance. These are C *suspicions/application gaps*, not proofs of contradiction or a claim that the abstract interface is uninhabited. See [the exact audit](../evidence/privacy-ledger-20261026/nonvacuity.txt).

## Atomic premise rows

Data/carrier/guard fields are shown first; none states deployment correctness. Fixed protocol Field/Fintype/Algebra instances are concrete imported constructions, not additional unsupplied typeclass arguments. In particular the template fields overwritten by base/wire remain visible for inventory but are not open theorem laws.

| ID / name | Defined at (file#decl) | Plain-English meaning / status | Class | Owner | Removing job / branch | Evidence |
|---|---|---|:---:|---|---|---|
| V001 / `CommitHandle` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Commitment-handle type; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V002 / `Aux` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Auxiliary output type; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V003 / `outputs` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Statement/challenge-to-Aux function; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V004 / `x` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Chosen public statement and handles; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V005 / `observer_program` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Adaptive query program on disclosed view and prior oracle history; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V006 / `rust.Adversary` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Adversary type; no Nonempty instance required; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V007 / `rust.RealRand` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Runtime random carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V008 / `rust.IdealRand` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Unused runtime ideal random carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V009 / `rust.real` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Runtime real experiment for all h/B/outputs/adv/x/w; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V010 / `rust.ideal` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Runtime ideal experiment; not used by this endpoint; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V011 / `rust.observe` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | Complete Boolean decision on ROMView; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V012 / `Fintype rust.RealRand` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Finite enumeration supporting uniform mean; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V013 / `Nonempty rust.RealRand` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#privacy_headline_deployed` | Explicit inhabitance prevents an empty real-random carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V014 / `template.Cm` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Commitment coins type (overwritten by base); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V015 / `template.finCm` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Finite commitment coins (overwritten); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V016 / `template.neCm` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Nonempty commitment coins (overwritten); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V017 / `template.Tab` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Oracle-table type (subsequently specialized); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V018 / `template.finTab` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Finite oracle tables; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V019 / `template.neTab` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Nonempty oracle tables; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V020 / `template.look` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Oracle lookup function; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V021 / `template.frame` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | 27 semantic frames; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V022 / `template.payload` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Four opening payloads; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V023 / `template.final` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Final message encoding; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V024 / `template.pubBytes` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Public-statement encoding; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V025 / `template.vtag` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | View tag; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V026 / `template.dec` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Challenge decoder; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V027 / `template.kstarOf` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Selected QueryScan completion index; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V028 / `template.comLog` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Commitment log (overwritten by PhaseWireLog2Bin.log); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V029 / `template.failView` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Fixed failure view; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V030 / `template.qmax` | `docs/research/v8-r0-zk-20261009/lean/R1Z/GamesR1.lean#R1Wire` | Observer fuel cap (specialized to 2^64); data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V031 / `refinement.cp.S` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | Common coupling carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V032 / `refinement.cp.finS` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | Finite common carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V033 / `refinement.cp.nonemptyS` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | Nonempty common carrier; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V034 / `refinement.cp.toR` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | Map common coins to rust.RealRand; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V035 / `refinement.cp.toM` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | Map common coins to (source.RealRand × seed) × fuel tape; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V039 / `bad-guard.realBad` | `docs/research/v8-r0-zk-20261009/lean/R1Z/QueryScanRealLazyBound.lean#realBad` | Selected first-stop Q22 parser returns error on the realVector attempt blocks; not an arbitrary source-failure predicate; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V040 / `bad-guard.realSeedQueries` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#realSeedQueries` | Only adversary query suffix: first good published view/log, or failView and empty log on no good attempt; capped runLog; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V041 / `bad-guard.seedGuess` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSeedEvent19.lean#augmented` | Some adversary query has domain-plus-secret-seed prefix; answer remains in Entry but seedPoint tests address; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V042 / `bad-guard.fuel` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFuelJoin22.lean#bad` | At attempt index zero only, one of 24 retained five-draw coordinates is all zero; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V086 / `RWireBatches.fib` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | SAME two normalized batch fibre sets; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V087 / `RWireBatches.reads` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | SAME two normalized ordered read lists; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V089 / `R_wire_coin_carrier` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1AcctModel.lean#wire_coins` | Fixed equivalence Cm ≃ RIdx→OracleAnswer, constructed by Equiv.refl; inverse laws belong to equivalence; data/typing only, no security law | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |

The remaining theorem-side rows include open coupling laws, C checks, proved internal laws and carried relation-domain guards. “model-proved” does not mean proved for shipped Rust.

| ID / name | Defined at (file#decl) | Plain-English meaning / status | Class | Owner | Removing job / branch | Evidence |
|---|---|---|:---:|---|---|---|
| V036 / `refinement.cp.meanR` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | For every rational test, the SAME cp.toR push-forward is exactly uniform on rust.RealRand | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V037 / `refinement.cp.meanM` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsAbort.lean#Coupling` | For every rational test, the SAME cp.toM push-forward is exactly uniform on ((model coins × uniform 256-bit seed) × 24 five-word fuel draws) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V038 / `refinement.agreement` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFuelJoin22.lean#RunJoin` | For every common sample outside the fixed union bad event, equality of the complete ROMView AND observer decision; same adv,w and public-equality guard | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V043 / `observerMap.program` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RomObserverBin.lean#observerMap` | observerMap.prog is exactly observer_program adv; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V044 / `observerMap.decision` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RomObserverBin.lean#observerMap` | observerMap.decide is exactly rust.observe adv; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V045 / `deployed rust instance` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean#RustRealRefinement` | C (vacuity/source-instance suspect): rust is a free FSExperiments parameter; no deployed-prover certificate is supplied here. Nonempty RealRand is explicit, but does not identify any actual implementation | C | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | nonvacuity.txt |
| V046 / `adversary domain inhabitance` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#FSExperiments` | C (vacuity suspect only): rust.Adversary may be empty; the universal privacy assertion then has no adversary cases | C | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | nonvacuity.txt |
| V047 / `matching witness/public fibre` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderCanonical.lean#Instance` | C (vacuity suspect only): for arbitrary x there may be no canonical RspendPlus instance with public=x.1; real refinement and advantage are then vacuous on that x | C | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | nonvacuity.txt |
| V048 / `BuilderPremises.PublicBase.anchor` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Every anchor limb lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V049 / `BuilderPremises.PublicBase.nullifier` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Every nullifier limb lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V050 / `BuilderPremises.PublicBase.assetId` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Asset ID lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V051 / `BuilderPremises.PublicBase.recipient` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Every present recipient limb lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V052 / `BuilderPremises.PublicBase.change` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Every change limb lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V053 / `BuilderPremises.PublicBase.withdrawalAmount` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Every present amount lies in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V054 / `BuilderPremises.PublicBase.snapshotFrontier` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | All snapshot-frontier limbs lie in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V055 / `BuilderPremises.PublicBase.nextRoot` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | Next-root limbs lie in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V056 / `BuilderPremises.PublicBase.nextFrontier` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PublicBase` | All next-frontier limbs lie in F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V057 / `BuilderPremises.BuilderSoundOn.baseTyped` | `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestValidity.lean#HonestBuilderSound` | All columns below 26 are F-valued; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V058 / `BuilderPremises.BuilderSoundOn.lanes` | `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestValidity.lean#HonestBuilderSound` | Every non-copy lane i<28 vanishes at every row and lam/chi; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V059 / `BuilderPremises.BuilderSoundOn.helperSum` | `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestValidity.lean#HonestBuilderSound` | Full helper sum is zero for every lam/chi; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V060 / `BuilderPremises.BuilderSoundOn.helperInactive` | `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestValidity.lean#HonestBuilderSound` | Inactive-row helper sum is zero for every lam/chi; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V061 / `CallerLaw.blocks₁` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#CallerLaw` | First source block count equals fixed E₁; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V062 / `CallerLaw.blocks₂` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#CallerLaw` | Second source block count equals fixed E₂; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V063 / `CallerLaw.quotient` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#CallerLaw` | There exists ONE tape-coordinate equivalence; all input decodes agree with quotientDecoder mapped by it; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V064 / `budgets.counter₁` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | Pr.E₁ ≤ 2^64; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V065 / `budgets.counter₂` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | Pr.E₂ ≤ 2^64; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V066 / `budgets.stream₁` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | 16*L₁ ≤ 8*Pr.E₁; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V067 / `budgets.stream₂` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | 16*L₂ ≤ 8*Pr.E₂; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V068 / `budgets.count₁` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | L₁ ≤ 45056; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V069 / `budgets.count₂` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | L₂ = 4096; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V070 / `budgets.blocks-bound₁` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | Pr.E₁ ≤ 2*L₁; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V071 / `budgets.blocks-bound₂` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#budgets` | Pr.E₂ ≤ 2*L₂; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V072 / `fibres` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#fibres` | Every SourceTape fibre has the same quotientFibreSize; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V073 / `exhaustion` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitCallerInstance.lean#exhaustion` | Decoder none implies stream1 exhausted OR stream2 exhausted; disjunction retained as one atomic event law; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | readable-20002.log |
| V074 / `PackField.i-square` | `docs/research/v8-r0-zk-20261009/lean/R0Z/K4.lean#PackField` | B.i² belongs to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/PrivacyR1Headline.lean.txt |
| V075 / `PackField.u-square.a` | `docs/research/v8-r0-zk-20261009/lean/R0Z/K4.lean#PackField` | The SAME existential a belongs to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/PrivacyR1Headline.lean.txt |
| V076 / `PackField.u-square.b` | `docs/research/v8-r0-zk-20261009/lean/R0Z/K4.lean#PackField` | The SAME existential b belongs to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/PrivacyR1Headline.lean.txt |
| V077 / `PackField.u-square.eq` | `docs/research/v8-r0-zk-20261009/lean/R0Z/K4.lean#PackField` | B.u²=a+B.i*b for those SAME a,b; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/PrivacyR1Headline.lean.txt |
| V078 / `basis.indep.a` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PackBasis` | With SAME a,b,c,d in F and packed sum zero, coefficient a is zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V079 / `basis.indep.b` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PackBasis` | With SAME a,b,c,d in F and packed sum zero, coefficient b is zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V080 / `basis.indep.c` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PackBasis` | With SAME a,b,c,d in F and packed sum zero, coefficient c is zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V081 / `basis.indep.d` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CoreExt.lean#PackBasis` | With SAME a,b,c,d in F and packed sum zero, coefficient d is zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V082 / `RWireBatches.concatenation` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | Open list equals ordered batch0 ++ batch1; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V083 / `RWireBatches.nodup` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | Each batch read list is duplicate-free; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V084 / `RWireBatches.coverage` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | Batch read membership iff openedQ for that batch fibre; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V085 / `RWireBatches.fibre_union` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean#RWireBatches` | Full open fibre equals batch0 union batch1; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V088 / `R_wire_D80_ordered_log` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PhaseWireLog2Bin.lean#ordered_log` | For every canonical witness/tape/challenges, complete comLog equals ordered grammar/answer map over openList; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V090 / `test_bound.test.nonnegative` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#bit` | Observer bit is ≥0; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V091 / `test_bound.test.atmostone` | `docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean#bit` | Observer bit is ≤1; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V092 / `realSeedQueries.length` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitObserverQueries19.lean#real_bound` | Adversary-only suffix length ≤2^64 on every branch, including all-failed attempts; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | consumers-20005.log |
| V093 / `Admitted.publicCorr.variant` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Rust variant equals public variant; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V094 / `Admitted.publicCorr.asset` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Lifted asset equals assetId; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V095 / `Admitted.publicCorr.next` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Next pair index equals public index; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V096 / `Admitted.publicCorr.frontier` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Each Rust frontier digest lifts to its public digest; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V097 / `Admitted.publicCorr.empty` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Each Rust empty digest lifts to the frozen empty root; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V098 / `Admitted.publicCorr.frontierCanon` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Each frontier word is below p; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V099 / `Admitted.publicCorr.emptyCanon` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#PubCorr` | Each empty-root word is below p; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V100 / `Admitted.words.inputValue` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#WitnessOk` | Input value <2^30; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V101 / `Admitted.words.outputValue` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#WitnessOk` | Output value <2^30; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V102 / `Admitted.words.changeValue` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#WitnessOk` | Change value <2^30; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V103 / `Admitted.words.bits` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#WitnessOk` | All 24 path directions are 0 OR 1; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V104 / `Admitted.words.sibs` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderWitness.lean#WitnessOk` | All 24 sibling digest words are below p; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V105 / `Admitted.semantic.witBase.sk` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | sk coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V106 / `Admitted.semantic.witBase.salt` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | salt coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V107 / `Admitted.semantic.witBase.path` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | path coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V108 / `Admitted.semantic.witBase.pairOccupied` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | pairOccupied coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V109 / `Admitted.semantic.witBase.pairSecond` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | pairSecond coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V110 / `Admitted.semantic.witBase.pairInverse` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | pairInverse coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V111 / `Admitted.semantic.witBase.recipientOwner` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | recipientOwner coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V112 / `Admitted.semantic.witBase.recipientSalt` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | recipientSalt coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V113 / `Admitted.semantic.witBase.changeOwner` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | changeOwner coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V114 / `Admitted.semantic.witBase.changeSalt` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelBase.lean#WitnessBase` | changeSalt coordinates belong to F; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V115 / `Admitted.semantic.aux.conservation` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Input value = output + change; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V116 / `Admitted.semantic.aux.pairValid.boolean` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Occupied flag is Boolean; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V117 / `Admitted.semantic.aux.pairValid.inverse` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | commitment[7]*inverse = occupied; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V118 / `Admitted.semantic.aux.pairValid.emptyInverse` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Empty occupancy forces inverse zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V119 / `Admitted.semantic.aux.pairValid.emptyCommitment` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Empty occupancy forces every commitment limb zero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V120 / `Admitted.semantic.aux.spendable` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Selected right branch implies occupied second slot; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V121 / `Admitted.semantic.aux.changeSentinel` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Transfer implies change digest limb7 nonzero; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V122 / `Admitted.semantic.aux.amount` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelAux.lean#AuxPremises` | Withdrawal present amount equals output value; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V123 / `Admitted.semantic.digest.anchor` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Anchor equals model membership root; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V124 / `Admitted.semantic.digest.nullifier` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Nullifier equals model digest; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V125 / `Admitted.semantic.digest.recipient` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Present recipient equals model recipient digest; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V126 / `Admitted.semantic.digest.change` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Change equals model change digest; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V127 / `Admitted.semantic.digest.nextRoot` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Next root equals model append recurrence at20; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V128 / `Admitted.semantic.digest.carry` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelDigest.lean#DigestPremises` | Present carry frontier equals append recurrence at digestCarry; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V129 / `Admitted.semantic.pairRight` | `docs/research/v8-r0-zk-20261009/lean/R0Z/BuilderModelCopyMisc.lean#PairRight` | Second pair commitment is ordered input-leaf right child; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V130 / `canonical.Instance.RspendPlus.transfer.recipient` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Transfer recipient is present; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V131 / `canonical.Instance.RspendPlus.transfer.noAmount` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Transfer withdrawalAmount is none; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V132 / `canonical.Instance.RspendPlus.withdrawal.noRecipient` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Withdrawal recipient absent; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V133 / `canonical.Instance.RspendPlus.withdrawal.amount` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Withdrawal amount present; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V134 / `canonical.Instance.RspendPlus.withdrawal.nonzero` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Withdrawal amount is not some zero; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V135 / `canonical.Instance.RspendPlus.input.valid.boolean` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Input second occupancy is Boolean; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V136 / `canonical.Instance.RspendPlus.input.valid.inverse` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Input occupancy inverse equation; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V137 / `canonical.Instance.RspendPlus.input.valid.emptyInverse` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Input empty inverse equation; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V138 / `canonical.Instance.RspendPlus.input.valid.emptyCommitment` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | All empty second-commitment limbs zero; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V139 / `canonical.Instance.RspendPlus.input.spendable` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Selected pair slot occupied; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V140 / `canonical.Instance.RspendPlus.input.commitment` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Selected commitment equals owned note commitment; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V141 / `canonical.Instance.RspendPlus.input.sibling` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | First path sibling is the OTHER member of this same pair; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V142 / `canonical.Instance.RspendPlus.input.nullifier` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Nullifier binds secret key and salt; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V143 / `canonical.Instance.RspendPlus.input.membership` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | 24-level note membership root equals anchor; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V144 / `canonical.Instance.RspendPlus.conservation` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Input=output+change; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V145 / `canonical.Instance.RspendPlus.change` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Change binds change commitment; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V146 / `canonical.Instance.RspendPlus.variant.transfer` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Present recipient binds recipient commitment; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V147 / `canonical.Instance.RspendPlus.variant.withdrawal` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Present withdrawal amount equals output value; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V148 / `canonical.Instance.RspendPlus.append.outputPair` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | SAME existential pair equals outputPair; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V149 / `canonical.Instance.RspendPlus.append.nextRoot` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Next root binds that SAME pair at depth20; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V150 / `canonical.Instance.RspendPlus.append.carry` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Carry frontier binds that SAME pair; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V151 / `canonical.Instance.RspendPlus.sentinel` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSpendRelation.lean#RspendPlus` | Transfer implies public change limb7 nonzero; carried honest-domain guard, not proof of existence for arbitrary x | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V155 / `real-self.cp.meanR` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identity self-join first marginal; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V156 / `real-self.cp.meanM` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identity self-join second marginal; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V157 / `real-self.agreement` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identical real model functions agree; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V158 / `ideal-self.cp.meanR` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identity ideal self-join first marginal; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V159 / `ideal-self.cp.meanM` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identity ideal self-join second marginal; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V160 / `ideal-self.agreement` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFixedObserver.lean#self_join` | Identical ideal model functions agree; proved for the fixed canonical model, deployment association remains separate | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | fields-20004.log |
| V270 / `Formatter axiom route` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean#ExternalTypes` | C (inadmissible route): imported Aeneas.Std.core.fmt.Formatter axiom is forbidden and unselected. Caller op85 independence is proved, but does not create a generic native Formatter representation | C | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-design.md |


## Deployment obligations and overlap

The handoff snapshots are pinned by full branch revisions in [handoff-pins.json](../evidence/privacy-ledger-20261026/handoff-pins.json); only `git show` was used, with no live sibling worktree access. `prover-rw14` names the current rw branch job even where its retained historical documents use older allocation labels. New pv job branch pins were not supplied; the job names are accountable destinations, not fabricated branch identities.

The rw query continuation establishes source factorization, grouped Q22 policy, materialization and finite publication control, and installs the query component through retries. Its latest P6 handoff installs source/P6 callbacks225,51,120,254 out of the prior39, leaving **35**. Those35 are marked on the SAME operation rows below (all are also in the dict sibling’s99 remaining operations). The sibling has **163/262 selected source/value entries, 26/28 type values**. These are overlapping selectors on different branch histories: no checked union is assumed. A selected source equation is not automatically full native effect adequacy, and a nominal type-value interpretation is not a live OS owner/world invariant. Candidate source tables retain different checkpoints (8→74→107/111 etc.); the latest handoff is used for each scoped claim, not added together into a completion score.

Two callbacks merit explicit qualifications. Compression remains uninstalled despite passing owned-reference finite control: its native comparisons timed out. `core.fmt.Formatter` is still an open generic representation; the forbidden Aeneas Formatter axiom is unselected, and complete op85 caller independence plus the scoped17-variant sink check does not install that representation. File’s selected signed32 value carrier does not prove OS ownership. The complete proof/audit data equation, PrefixContract, BodyContract and native effect/entropy joins remain open.

| ID / name | Defined at (file#decl) | Plain-English meaning / status | Class | Owner | Removing job / branch | Evidence |
|---|---|---|:---:|---|---|---|
| V152 / `source-identification.public_eq` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSource.lean#SourceIdentification` | Actual builder public projection equals canonical map | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/BuilderSource.lean.txt |
| V153 / `source-identification.build_eq` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSource.lean#SourceIdentification` | Actual builder raw trace equals canonical merged trace | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/BuilderSource.lean.txt |
| V154 / `source-identification.transport_eq` | `docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderSource.lean#SourceIdentification` | Actual S2 transport equals π/D18 | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/BuilderSource.lean.txt |
| V161 / `PrefixContract` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#PrefixContract` | Pointwise complete prefix Result/state equality for every nonce/bytes/state; retain serializer, reservation address, failures | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/RealR1_OuterOwner.lean.txt |
| V162 / `BodyContract` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#BodyContract` | Pointwise complete successful/rejected proof/audit/Result/state equality, not just output success | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/RealR1_OuterOwner.lean.txt |
| V163 / `whole proof/audit data equation` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Replace the supplied equality in BodyData.refinement_of_data with actual source/model proof | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V164 / `compression correspondence` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Prove shipped compress equals extracted owned reference; prior Kani timeouts do not supply it | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V165 / `native representation` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Associate native carriers with selected value interpretations, including constructor domains | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V166 / `native ABI/features` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Associate actual calling convention and compilation feature profile with retained contracts | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V167 / `native effects` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Transport ordered ROM/TLS, failure/divergence, Drop/unwind and world state | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V168 / `entropy/retry adequacy` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6BodyData.lean#refinement_of_data` | Compose full sixteen-call64-byte fill histories and outer eight attempts including errors/partial writes/provider state; pure fixed dictionaries do not model this | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-success.md; rw-p6-final.json |
| V169 / `op3 core.mem.take` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 3 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V170 / `op4 core.mem.drop` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 4 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V171 / `op14 std.fs.File.open` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 14 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V172 / `op15 std.fs.File.sync_all` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 15 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V173 / `op16 std.io.Write.write_all.default` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 16 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V174 / `op18 std.fs.File.Insts.StdIoWrite.write` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 18 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V175 / `op22 std.fs.OpenOptions.open` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 22 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V176 / `op23 std.io.error.Error.kind` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 23 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V177 / `op25 std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 25 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V178 / `op26 std.path.Path.join` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 26 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V179 / `op28 alloc.string.String.Insts.CoreConvertAsRefPath.as_ref` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 28 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V180 / `op29 std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 29 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V181 / `op30 alloc.string.String.with_capacity` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 30 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V182 / `op31 alloc.string.String.push_str` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 31 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V183 / `op32 alloc.vec.Vec.try_reserve_exact` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 32 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V184 / `op33 alloc.vec.Vec.pop` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 33 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V185 / `op34 alloc.vec.Vec.is_empty` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 34 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V186 / `op35 alloc.vec.Vec.Insts.CoreDefaultDefault.default` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 35 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V187 / `op36 Array.Insts.CoreConvertTryFromVecVec.try_from` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 36 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V188 / `op37 aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 37 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V189 / `op40 aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 40 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V190 / `op41 aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 41 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V191 / `op43 aspis_core.field.wide_exact.WideExact.impl.c0` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 43 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V192 / `op44 aspis_core.field.wide_exact.WideExact.impl.c1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 44 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V193 / `op49 aspis_core.field.wide_exact.WideExact.to_limbs` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 49 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V194 / `op50 aspis_core.field.wide_exact.WideExact.from_le_bytes` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 50 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V195 / `op51 aspis_core.field.wide_exact.WideExact.to_le_bytes` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 51 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V196 / `op60 aspis_core.field.CM31.new` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 60 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V197 / `op71 aspis_core.field.QM31.from_le_bytes` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 71 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V198 / `op72 aspis_core.field.QM31.write_le_bytes` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 72 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V199 / `op77 aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 77 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V200 / `op78 aspis_core.r0.domain.fibre_point` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 78 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V201 / `op79 aspis_core.r0.encoder.eval_message` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 79 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V202 / `op80 aspis_core.r0.fold.phi_inverse` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 80 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V203 / `op81 aspis_core.r0.heap.filled` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 81 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V204 / `op82 aspis_core.r0.merkle.C1_TAG` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 82 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V205 / `op83 aspis_core.r0.merkle.C2_TAG` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 83 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V206 / `op84 aspis_core.r0.merkle.leaf` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 84 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V207 / `op85 aspis_core.r0.Error.Insts.CoreFmtDebug.fmt` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 85 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V208 / `op86 aspis_core.r0.opening.LANES` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 86 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V209 / `op100 aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 100 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V210 / `op101 aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 101 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V211 / `op105 aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 105 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V212 / `op107 aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 107 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V213 / `op109 aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 109 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V214 / `op110 aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 110 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V215 / `op111 aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 111 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V216 / `op114 aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 114 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V217 / `op117 aspis_core.state_only_hiding.state_only_selected_mask_value` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 117 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V218 / `op118 aspis_core.state_only_prefix.r0.statement_points` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 118 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V219 / `op120 aspis_core.state_only_sumcheck.state_only_boundary_sum` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 120 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V220 / `op121 aspis_core.state_only_sumcheck.evaluate_state_only_polynomial` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 121 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V221 / `op122 Array.Insts.ZeroizeZeroize.zeroize` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 122 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V222 / `op123 zeroize.Zeroize.Blanket.zeroize` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 123 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V223 / `op127 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 127 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V224 / `op128 zeroize.Zeroizing.new` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 128 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V225 / `op129 getrandom.fill` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 129 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V226 / `op130 zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 130 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V227 / `op131 zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 131 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V228 / `op132 aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 132 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V229 / `op133 aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 133 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V230 / `op134 aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 134 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V231 / `op205 sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 205 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V232 / `op208 sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 208 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V233 / `op209 block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 209 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V234 / `op212 digest.digest.Digest.Blanket.finalize` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 212 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V235 / `op215 digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 215 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V236 / `op216 digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 216 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V237 / `op217 digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 217 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V238 / `op219 digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 219 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V239 / `op222 aspis_statement.constraints_v4.multilinear_evaluate_qm31` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 222 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V240 / `op223 aspis_statement.logup.compress_tagged_tuple` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 223 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V241 / `op224 aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 224 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V242 / `op225 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 225 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V243 / `op226 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 226 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V244 / `op227 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 227 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V245 / `op228 aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 228 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V246 / `op229 aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 229 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V247 / `op230 aspis_statement.state_only_semantic.state_only_copy_helper_sum` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 230 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V248 / `op231 aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 231 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V249 / `op232 aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 232 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V250 / `op235 multiproof.LEAF_BITS` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 235 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V251 / `op236 multiproof.MAX_BATCH` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 236 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V252 / `op239 r1_wire.CLAIMS` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 239 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V253 / `op240 r1_wire.LANES` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 240 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V254 / `op246 multiproof.binary_parent` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 246 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V255 / `op247 trace.value` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 247 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V256 / `op249 sampler.gamma_sample` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 249 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V257 / `op250 sampler.ordinary_sample` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 250 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V258 / `op251 weights.Weights.materialize` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 251 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V259 / `op252 weights.Weights.new` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 252 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V260 / `op253 weights.Weights.raw` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 253 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V261 / `op254 weights.powers` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 254 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V262 / `op255 transport.Variant.coefficients` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 255 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V263 / `op257 host_work.map` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 257 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V264 / `op258 ct_pole.all_slots_clear` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 258 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V265 / `op259 sampler.circle_sample` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 259 with Result/failure/divergence and required callback/value law; body-overapproximation=True; ALSO one of rw14 remaining35 source callbacks (same op, counted once) | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 + prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V266 / `op260 r1_wire.DOMAIN` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 260 with Result/failure/divergence and required callback/value law; body-overapproximation=True | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V267 / `op261 std.fs.File.Insts.StdIoWrite.write_all` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean#ExternalFuns` | Install exact selected operation 261 with Result/failure/divergence and required callback/value law; body-overapproximation=False | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; rw-next-final.json; rw-p6-final.json |
| V268 / `type3 std.io.error.Error` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean#ExternalTypes` | Supply complete native type/value/effect interpretation; dynamic payload/vtable or Formatter association remains uninstalled | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; dict-design.md |
| V269 / `type27 core.fmt.Formatter` | `docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean#ExternalTypes` | Supply complete native type/value/effect interpretation; dynamic payload/vtable or Formatter association remains uninstalled | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; dict-design.md |
| V271 / `File owner/world` | `docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FileCarrier.lean#type0_installed` | Nonnegative signed32 File value is selected; live descriptor ownership, nondeterministic OS results and exactly-once Drop/world transport still required | P | stream B | prover-dict5 · codex/cx-prover-dict-20261026 | dict-entries.md; dict-design.md |
| V336 / `E1 native conditioning` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#PrefixContract` | Associate actual getrandom calls, partial writes/status/provider state and64-byte carrier with E1; no uniformity of pure callback models inferred | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-entropy.json; rw-query.md; LOG-excerpts.md |
| V337 / `E2 native instance` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#PrefixContract` | Associate actual reservation create/write/fsync/ledger lifecycle with the SAME E2 world; no law invented for callbacks | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-entropy.json; rw-query.md; LOG-excerpts.md |
| V338 / `byte-blind faults` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#PrefixContract` | Adversarial schedules/initial ledger/additions must not inspect secret contents; retain adaptive public policy | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-entropy.json; rw-query.md; LOG-excerpts.md |
| V339 / `entropy kernels` | `docs/research/v8-r0-zk-20261009/lean/R1Z/RealR1_OuterOwner.lean#PrefixContract` | Install normalized next-context/substochastic retry laws at exact conditional history frame; 2^-4080/2^-4077 are conditional model results | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | rw-entropy.json; rw-query.md; LOG-excerpts.md |

The native effect cut below is a deliberately explicit overlap appendix:41 LocalLeaves fields from the material-expanded cut plus16 TypeLeaves. The coarser native-body cut has35 fields because its mask-material caller groups seven expanded operations into one (net reduction6); both exact source snapshots are retained. Neither41 nor35 is the current remaining35 successful-body callback count. They describe different, overlapping syntactic interfaces. These57 rows are excluded from the “remaining obligation/trust/vacuity families” subtotal. Functional standard-library trust does not absorb the trace/world obligations in this appendix.

| ID / name | Defined at (file#decl) | Plain-English meaning / status | Class | Owner | Removing job / branch | Evidence |
|---|---|---|:---:|---|---|---|
| V272 / `native-cut.material.f0 core.option.Option.Insts.CoreCmpPartialEqOption.eq` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V273 / `native-cut.material.f1 std.io.error.Error.kind` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V274 / `native-cut.material.f2 Array.Insts.CoreConvertTryFromVecVec.try_from` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V275 / `native-cut.material.f3 aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V276 / `native-cut.material.f4 aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V277 / `native-cut.material.f5 aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V278 / `native-cut.material.f6 aspis_core.field.wide_exact.WideExact.ZERO` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V279 / `native-cut.material.f7 aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V280 / `native-cut.material.f8 aspis_core.field.QM31.ZERO` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V281 / `native-cut.material.f9 aspis_core.r0.merkle.C1_TAG` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V282 / `native-cut.material.f10 aspis_core.r0.merkle.C2_TAG` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V283 / `native-cut.material.f11 aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V284 / `native-cut.material.f12 Array.Insts.ZeroizeZeroize.zeroize` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V285 / `native-cut.material.f13 zeroize.Zeroize.Blanket.zeroize` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V286 / `native-cut.material.f14 zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V287 / `native-cut.material.f15 zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V288 / `native-cut.material.f16 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V289 / `native-cut.material.f17 zeroize.Zeroizing.new` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V290 / `native-cut.material.f18 aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V291 / `native-cut.material.f19 aspis_prover.state_only_hiding.sample_mask_h1_padding` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V292 / `native-cut.material.f20 aspis_prover.state_only_hiding.sample_mask_g` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V293 / `native-cut.material.f21 aspis_prover.state_only_hiding.sample_mask_columns` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V294 / `native-cut.material.f22 aspis_prover.state_only_hiding.sample_mask_cells` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V295 / `native-cut.material.f23 aspis_prover.state_only_hiding.first_inactive_row` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V296 / `native-cut.material.f24 aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V297 / `native-cut.material.f25 aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V298 / `native-cut.material.f26 aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V299 / `native-cut.material.f27 aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V300 / `native-cut.material.f28 aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V301 / `native-cut.material.f29 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V302 / `native-cut.material.f30 aspis_statement.state_only_semantic.state_only_copy_helper_sum` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V303 / `native-cut.material.f31 aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V304 / `native-cut.material.f32 host_commitment.EncodingDomain.new` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V305 / `native-cut.material.f33 host_semantic.build_with_material` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V306 / `native-cut.material.f34 prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V307 / `native-cut.material.f35 prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V308 / `native-cut.material.f36 prover.prove_from_semantics` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V309 / `native-cut.material.f37 prover.derive_private_salts` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V310 / `native-cut.material.f38 prover.semantic_error` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V311 / `native-cut.material.f39 prover.audit_masks` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V312 / `native-cut.material.f40 prover.fixed_k_column` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyLeaves.lean#LocalLeaves` | Native effect/callback association for this retained cut field; overlaps corresponding operation/source rows; no additional privacy axiom **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngMaterialBodyLeaves.lean.txt; sources/ProverRwRngNativeBodyLeaves.lean.txt; rw-entropy.json |
| V313 / `native-cut.t0 std.io.error.Error` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V314 / `native-cut.t1 std.path.PathBuf` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V315 / `native-cut.t2 aspis_core.circle.SecureCirclePoint` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V316 / `native-cut.t3 aspis_core.r0.Error` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V317 / `native-cut.t4 aspis_core.state_only_prefix.r0.Error` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V318 / `native-cut.t5 aspis_core.state_only_prefix.r0.Challenges` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V319 / `native-cut.t6 aspis_prover.state_only_hiding.StateOnlyMaskMaterial` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V320 / `native-cut.t7 aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V321 / `native-cut.t8 aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V322 / `native-cut.t9 aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V323 / `native-cut.t10 aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V324 / `native-cut.t11 host_commitment.EncodingDomain` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V325 / `native-cut.t12 host_commitment.Commitment` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V326 / `native-cut.t13 host_commitment.PrivateSalts` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V327 / `native-cut.t14 r1_wire.Error` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |
| V328 / `native-cut.t15 host_wire.SemanticTranscript` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyTypes.lean#TypeLeaves` | Native representation/effect association for this retained type cut; overlaps full dictionary representations; type alone gives no law **OVERLAP: do not add as independent gate.** | P | stream B | prover-rw14 · codex/cx-prover-rw-20261023 | sources/ProverRwRngNativeBodyTypes.lean.txt; rw-entropy.json |

The rows below include environment trust, concrete environment association, L1/L2/L3, adoption, client and replay obligations. E2 is split into six leaves because its atomic field contains an iff and two further conjuncts and durable contains two conjuncts. E2 is external trust **only** in its named LOG D148 scope; actual caller/ledger association remains P. E1 is trust **only** at the successful getrandom64 boundary named in D147, never a license to assert independent/uniform opaque callbacks, successful draws, arbitrary retry probabilities or entropy-provider hidden-state transport. This older E1 96-byte API has a64-byte proof-account specialization; this endpoint does not silently choose the old route.

| ID / name | Defined at (file#decl) | Plain-English meaning / status | Class | Owner | Removing job / branch | Evidence |
|---|---|---|:---:|---|---|---|
| V329 / `E1 successful64-byte conditional law` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitPublicNonce40.lean#E1` | Every successful getrandom64 return is uniform conditional on COMPLETE prior private/public context; no assumption of availability | T | external | retained LOG D147 OS getrandom boundary | fields-20004.log; LOG-excerpts.md |
| V330 / `E2.atomic.alreadyExists.forward` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | AlreadyExists implies path was present | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V331 / `E2.atomic.alreadyExists.reverse` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | Present path implies AlreadyExists | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V332 / `E2.atomic.created` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | Successful create leaves path present | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V333 / `E2.atomic.preserve` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | Create preserves all previously present paths | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V334 / `E2.durable.stored` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | Written/fsynced data is stored after the operation | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V335 / `E2.durable.persists` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitLedger36.lean#E2` | SAME written data stays stored in every future persists state | T | external | retained named E2 filesystem trust · LOG D148 | fields-20004.log; LOG-excerpts.md |
| V340 / `research rebase` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Rebase candidate onto research retaining adapter/H5 adoptions and rebind proofs | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V341 / `default ELF identity` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Rebuild and compare default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V342 / `devnet ELF identity` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Rebuild and compare devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V343 / `Pool ELF identity` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Rebuild and compare Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V344 / `absolute timing` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Quiet-host, pinned candidate proof time median <15s; report samples/profile/CPU | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V345 / `relative timing` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Median regression ≤10% against relevant pinned baseline; historical fixture ratios alone do not settle absolute gate | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V346 / `proved=shipped manifest` | `docs/research/v8-r0-zk-20261009/LOG.md#D169/D191` | Pin same source/features/toolchain/wire/parameters/native prover binary and every proof/extraction/Kani association; no historical certificate migration by name | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) | LOG-excerpts.md; rw-query.md; dict-design.md |
| V347 / `L1.native event producer` | `docs/research/v8-r0-zk-20261009/LOG.md#D163` | Refine actual entered/rejected/success/error/reservation/send/write events to ordered L1 model | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + prover-rw14 · codex/cx-prover-rw-20261023 | LOG-excerpts.md; l2-leaf-REPORT.md |
| V348 / `L1.joint mask/count/TLS/oracle` | `docs/research/v8-r0-zk-20261009/LOG.md#D163` | Prove joint law with publication and history, not marginal count symmetry | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + prover-rw14 · codex/cx-prover-rw-20261023 | LOG-excerpts.md; l2-leaf-REPORT.md |
| V349 / `L1.equal-circle integration` | `docs/research/v8-r0-zk-20261009/LOG.md#D163` | Compose equal-circle exception with complete rejected-prefix/event law | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + prover-rw14 · codex/cx-prover-rw-20261023 | LOG-excerpts.md; l2-leaf-REPORT.md |
| V350 / `L1.query-abort integration` | `docs/research/v8-r0-zk-20261009/LOG.md#D163` | Compose QueryScan exhaustion and observer/error prefixes | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + prover-rw14 · codex/cx-prover-rw-20261023 | LOG-excerpts.md; l2-leaf-REPORT.md |
| V351 / `L1.part47 composition` | `docs/research/v8-r0-zk-20261009/LOG.md#D163` | Compose model y1 byte image with native L1 experiment | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + prover-rw14 · codex/cx-prover-rw-20261023 | LOG-excerpts.md; l2-leaf-REPORT.md |
| V352 / `L2 F3 `prover/state_only_entropy.rs:202` `generate_for_mask_nonce`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Up to 16 OS draws, nonzero seed comparisons/short circuit, error prefix; joint environment/seed law under E1. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V353 / `L2 F3 `prover/state_only_entropy.rs:760,780,794,804` `Profile21SourceExpander::{new,next_word,m31,qm31}`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Refill positions, scalar rejection counts, four-limb early propagation and exhaustion, jointly with previously read ROM blocks. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V354 / `L2 F3 `prover/state_only_hiding.rs:330,350,361,371` `SeedExpander::{new,next_word,m31,qm31}`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Same seed/refill/limb/rejection history for mask derivation; field arithmetic uses CT leaves but sampling control is unchanged. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V355 / `L2 F3/F6 `probe/sim.rs:79,80,84` `Coins::{new,coin,nonzero}`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Simulator nonzero loops and coin-consumption prefixes, related to the real joint law rather than separately asserted independent. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V356 / `L2 F5 `probe/sampler.rs:8,21,45,102,111,121`; `probe/r1_wire.rs:194,209,256`; `probe/transcript.rs:23,31`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Challenge rank division/remainder, gamma carry and circle singular/subfield/fallback selection. `core/circle.rs:34,55` and `core/r0_transcript.rs:177` retain challenge-dependent validity/fallback branches. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V357 / `L2 F5 `statement/constraints_v4.rs:601,654,782`; `probe/host_semantic.rs:31,204`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Sparse ZERO/ONE suffix pruning, capacities, selected column addresses and point-claim interpolation, including prior FS coordinates. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V358 / `L2 F5 `core/r0_transcript.rs:202,216,305`; `probe/transcript.rs:35`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Duplicate history, accepted positions, early stop, returned stream advance and QueryScan exhaustion, not just the published accepted list. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V359 / `L2 F5/F6 `probe/prover.rs:253,266`; `probe/host_commitment.rs:220,229,242`; `probe/multiproof.rs:54,198,248,251`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Opening word/salt addresses, sort/dedup, sibling sharing, node lookups/counts, Vec growth and fixed-slot padding. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V360 / `L2 F6 `probe/prover.rs:307,354`; `z4/z9e.rs:50,90,184,196`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | P_R1 factoring through hidden-attempt challenges, certificate creation/checking, phase timers, caught panic and retry/error prefixes. TLS retention is disabled, but local phases and their work remain. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V361 / `L2 F6 `z4/z9c.rs:107,135,290,332`; `z4/z9d.rs:17,41,74,90,113`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Zero skips, pivot searches, row swaps, inverse branches, rank thresholds, certificate-sized allocations/indices, early stopping, conversion and matrix-product work. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V362 / `L2 F6 `z4/z9.rs:567,989,1010,1016`; `z4/z9b.rs:78,107`; `z4/probe.rs:2207,2214,2256`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Query-derived layout, lane counts/selection, relation functionals and raw/tail coefficient construction. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V363 / `L2 F6 `c3/build/src/lib.rs:108,317,358,539,820,918`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | The six `fill_*` entry points and their supporting arithmetic/selector/source loops, driven by challenge/certificate descriptors and dimensions. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V364 / `L2 F6 `c3/check/src/lib.rs:27,40,56,81,96,138,149,160,171,182,193,204,215,227,243,255,270,275,370,384,407`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Dot/image/pivot/entry/product/identity/echelon/permutation/null-vector/lift/half checks, arithmetic helpers and checker entry points; certificate-dependent selection, work and failure prefixes. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V365 / `L2 F6 `probe/sim.rs:99,114,133,358,368,396,439`` | `docs/research/100bit-spend-path-20261013/design/CT-KERNELS-20261022.md#F3/F5/F6 left to the simulatable-trace proof` | Full-byte BTree oracle-key comparison, insert/overwrite/collision/hit-set history, memoized opened/folded/leaf maps, parent sets, lazy callbacks and repeated-parent sharing. Existing functional collection laws do not prove their cost law. | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | ct-kernels.md; l2-leaf-REPORT.md |
| V366 / `L2 joint raw-input coupling` | `docs/research/v8-r0-zk-20261009/lean/R1Z/SideChannelL1JointCoupling.lean#joint agreement` | Retain public/history view AND full raw trace inputs on the SAME coupling outside charged bad events. completed_view/middle_completion and draw-count preservation do not supply this | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | l2-leaf-REPORT.md |
| V367 / `L2.F1 pole kernels` | `docs/research/v8-r0-zk-20261009/LOG.md#D162/D166` | Instantiate adopted constant-time arithmetic and two-run source trace at pole operands/callers | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + pv-rebase · assigned pv-rebase job (branch pin not supplied) | ct-kernels.md; LOG-excerpts.md |
| V368 / `L2.F2 witness kernels` | `docs/research/v8-r0-zk-20261009/LOG.md#D162/D166` | Instantiate adopted constant-time field kernels and witness-bearing loops/callers | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + pv-rebase · assigned pv-rebase job (branch pin not supplied) | ct-kernels.md; LOG-excerpts.md |
| V369 / `L2.production TLS gating` | `docs/research/v8-r0-zk-20261009/LOG.md#D162/D166` | Verify shipped selected feature disables instrumentation as promised; preserve needed abstract observer effects | P | stream B | pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) + pv-rebase · assigned pv-rebase job (branch pin not supplied) | ct-kernels.md; LOG-excerpts.md |
| V370 / `L3.compiler preservation` | `docs/research/v8-r0-zk-20261009/LOG.md#D162` | Pinned compiler/flags preserve proved source constant-time properties | T | external | retained D162 compiler/CPU constant-time trust | LOG-excerpts.md |
| V371 / `L3.CPU latency` | `docs/research/v8-r0-zk-20261009/LOG.md#D162` | Used instructions on pinned x86_64 Linux CPU have data-independent latency | T | external | retained D162 compiler/CPU constant-time trust | LOG-excerpts.md |
| V372 / `L3.platform pins` | `docs/research/v8-r0-zk-20261009/LOG.md#D162` | Pin x86_64 Linux native binary, compiler/flags and CPU model | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | LOG-excerpts.md; ct-kernels.md |
| V373 / `L3.disassembly audit` | `docs/research/v8-r0-zk-20261009/LOG.md#D162` | Audit actual compiled witness/pole kernels and call sites | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | LOG-excerpts.md; ct-kernels.md |
| V374 / `L3.dudect measurement` | `docs/research/v8-r0-zk-20261009/LOG.md#D162` | Run and retain timing tests with sample setup/statistics; measurements never prove absence of leakage | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + pv-l2-sim · assigned pv-l2-sim job (branch pin not supplied) | LOG-excerpts.md; ct-kernels.md |
| V375 / `TrustedStd.btree_empty` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_empty equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V376 / `TrustedStd.btree_insert_state` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_insert_state equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V377 / `TrustedStd.btree_insert_previous` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_insert_previous equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V378 / `TrustedStd.btree_get` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_get equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V379 / `TrustedStd.btree_iter_ordered` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_iter_ordered equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V380 / `TrustedStd.btree_entry_or_insert_with` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_entry_or_insert_with equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V381 / `TrustedStd.btree_set_from_iter_ordered` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_set_from_iter_ordered equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V382 / `TrustedStd.btree_len` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native btree_len equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V383 / `TrustedStd.slice_sort_ascending` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native slice_sort_ascending equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V384 / `TrustedStd.vec_dedup_adjacent` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Successful native vec_dedup_adjacent equals the stated functional collection specification; no cost law follows | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V385 / `TrustedStd.tls_live_key` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Actual live TLS access equals native TLS specification | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V386 / `TrustedStd.tls_single_thread` | `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTrustedStd24.lean#TrustedStd` | Designated schedule uses exactly the one retained thread | T | external | retained LOG D133/D145/D156/D157 standard-library trust | fields-20004.log; sources/ProverCommitTrustedStd24.lean.txt |
| V387 / `toolchain/P7` | `docs/research/v8-r0-zk-20261009/LOG.md#D42/D188` | Pinned compiler/linker/loader and source-to-artifact association trust boundary | T | external | retained named external boundary | LOG-excerpts.md; rw-query.md |
| V388 / `AeneasExtraction` | `docs/research/v8-r0-zk-20261009/LOG.md#D42/D188` | Rust source-to-Charon/Aeneas extracted semantics · D188; extracted bodies do not need invented per-call reproof | T | external | retained named external boundary | LOG-excerpts.md; rw-query.md |
| V389 / `Kani/P6 association` | `docs/research/v8-r0-zk-20261009/LOG.md#D42/D188` | Accepted native wrapper/runtime contracts tied to exact Kani/tool/source/features, bounded loops and no stubs | T | external | retained named external boundary | LOG-excerpts.md; rw-query.md |
| V390 / `Solana runtime` | `docs/research/v8-r0-zk-20261009/LOG.md#D42/D188` | Runtime account/instruction/transaction semantics for proof-account deployment; not a prover-model axiom | T | external | retained named external boundary | LOG-excerpts.md; rw-query.md |
| V391 / `classical ROM/P1` | `docs/research/v8-r0-zk-20261009/LOG.md#D42/D188` | Classical ideal shared random oracle used by privacy model, not a computational SHA-256 proof | T | external | retained named external boundary | LOG-excerpts.md; rw-query.md |
| V392 / `client.proof-account source route` | `crates/aspis-r1-cost-probe/src/RealR1_client.rs#prove_for_proof_accounts` | Actual client invokes prove_for_proof_accounts → generate_for_mask_nonce → prove_masked_retrying_with S2; source helper exists, deployment caller adoption still required | P | stream B | pv-client · assigned pv-client job (branch pin not supplied) | client-source.rs.txt; REAL-R1.md; LOG-excerpts.md |
| V393 / `client.adaptive proof-account policy` | `crates/aspis-r1-cost-probe/src/RealR1_client.rs#prove_for_proof_accounts` | Associate public nonce with retained proof-account key at every entered attempt, including rejected keys; policy may adapt to prior public history | P | stream B | pv-client · assigned pv-client job (branch pin not supplied) | client-source.rs.txt; REAL-R1.md; LOG-excerpts.md |
| V394 / `client.published account selection` | `crates/aspis-r1-cost-probe/src/RealR1_client.rs#prove_for_proof_accounts` | Upload/use the returned attempts-1 account and bind public bytes/proof to that account | P | stream B | pv-client · assigned pv-client job (branch pin not supplied) | client-source.rs.txt; REAL-R1.md; LOG-excerpts.md |
| V395 / `client.durable ledger lifecycle` | `crates/aspis-r1-cost-probe/src/RealR1_client.rs#prove_for_proof_accounts` | Share actual nonce store across calls; preserve fail-closed reuse, errors and durable state | P | stream B | pv-client · assigned pv-client job (branch pin not supplied) | client-source.rs.txt; REAL-R1.md; LOG-excerpts.md |
| V396 / `client.client integration receipt` | `crates/aspis-r1-cost-probe/src/RealR1_client.rs#prove_for_proof_accounts` | Pin and exercise actual caller/upload route and key retention, including failure/retry paths | P | stream B | pv-client · assigned pv-client job (branch pin not supplied) | client-source.rs.txt; REAL-R1.md; LOG-excerpts.md |
| V397 / `coherent privacy closure replay` | `AGENTS.md#Security and proof discipline §8` | One ordered source/manifest dependency replay for final adopted endpoint and actual instances; focused cached prints are insufficient | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + stream B lead | receipts.json; LOG-excerpts.md |
| V398 / `final axioms audit` | `AGENTS.md#Security and proof discipline §8` | Audit final endpoint and adopted instance dependency closure: only propext, Classical.choice, Quot.sound plus explicitly named external hypotheses; reject Formatter/sorryAx | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + stream B lead | receipts.json; LOG-excerpts.md |
| V399 / `release evidence binding` | `AGENTS.md#Security and proof discipline §8` | Tie replay/source/native/Kani/extraction/three-ELF/client/L1-L3 evidence to SAME final release revision | P | stream B | pv-rebase · assigned pv-rebase job (branch pin not supplied) + stream B lead | receipts.json; LOG-excerpts.md |

The D163 L1 results already establish ordered outcome records, retry-control erasure, conditional hazards/entry laws, capped two-seed symmetry, an ideal count law and generic joint-TV tools. The five remaining L1 families above are not discharged by those model results. For L2, the14 F3/F5/F6 rows are copied one-for-one from the candidate table; source locations refer to that pinned candidate rather than current worktree line numbers. The extra joint-input row is the common missing bridge, not a second trace-law charge.

The L2 leaf report already proves partial reference observations, two counterexamples to verdict/output⇒trace inference, and a generic joint event-count coupling bound/exact equality under full-input agreement. Seven passing small Kani scopes are historical source-expression checks (including division limb, seed comparison, sibling group, sparse coordinate, QueryScan comparison and pivot decision); none instantiates full native inputs or their joint distribution. Every kernel’s full simulatable trace remains OPEN. Sort/Vec/hash/allocation/panic costs and challenge-dependent callers are included, not excluded by the absence of direct witness reads in the leaves.

L3 remains two named compiler/CPU trust laws plus three distinct evidence deliverables. The ct-v2 report expressly claims **no disassembly or dudect result**. Its historical single fixture times are transfer41.7381→38.5119s and withdrawal38.9356→37.9546s, labelled single-sample proof-generation measurements, not L3 evidence. Its40dc7574…/12cb0bc2… verifier identities predate the current release pins. The dictionary handoff’s historical relative fixture ratios0.9984115/0.9560918 are also not a quiet median<15s certificate. rw candidate defaultd7d42f77… and devnet2b2a9f0e… diverge from current pins; Pool historically matches. All three identities and both timing gates must be reassessed on the SAME rebased candidate.

`RealR1_client.rs` already contains the narrow proof-account helper: it takes retained account public keys, uses Variant::S2, calls generate_for_mask_nonce and passes the durable store into prove_masked_retrying_with. That is source evidence, not a receipt that the deployed caller/uploader adopts this helper. The five client rows preserve adaptive public key choice, rejected key retention, selected account and ledger/error behavior.

Explicit duplication/consumption map (aliases are NOT extra rows):

| Deployment item | Same theorem-side family or nested fact | Counting treatment |
|---|---|---|
| Complete real RunJoin | V036/V037 exact marginals and V038 agreement | No second umbrella RunJoin row; component rows state work feeding these laws |
| Native entropy/ROM/TLS/body/observer association | V038 joint agreement plus V036–V037 same-carrier laws | Deployment subdeliverables overlap, not independent epsilon terms |
| Native builder public/trace/transport | source-identification.public_eq/build_eq/transport_eq vs proved BuilderPremises and canonical-domain leaves | Native association still P; model leaves remain proved/carried |
| Source block counts, equal fibres and exhaustion | CallerLaw and budgets/fibres/exhaustion | Model facts counted once; no claim actual entropy model follows from them |
| ModelRel.pubBase | Same nine BuilderPremises.PublicBase leaves | Alias, no second nine rows |
| Model real/ideal self-joins | Six self-join laws in theorem table | Already proved identity-coupling instances; no hidden external assumptions |
|35 rw remaining callbacks vs dict99 | Rows explicitly tagged “ALSO one of rw14 remaining35” | One op row per ID, not134 rows |
| Material/native type cuts |57 overlap appendix rows vs operation/native-effect/type rows | Explicit syntactic expansion, excluded from open subtotal |
| L1/L2 native joint input law | Joint history/raw inputs refine V038’s observable experiment | Generic partial trace proofs do not remove the law; costs not covered by TrustedStd |
| E1/E2 accepted abstract laws vs native instance | Named trust rows and separate P association rows | Different statements; do not call native association external trust |
| Final replay and axioms audit | Development receipts and final dependency closure | Focused print audit is current evidence, not a completed release gate |

The total at the top is the number of displayed syntactic rows, including data, carried honest guards, already-proved model families and57 flagged cut overlaps. The191-family open/trust/vacuity subtotal excludes those four categories. It still contains intentionally overlapping implementation subdeliverables and four C diagnoses; it is not191 independent gates or a numerical probability bound. Owner totals use only {stream B, external}. No owner/job assignment implies acceptance or completion.


## Validation and LOG consistency

Five Lean compiler invocations out of15 (four exit0, one changed-import diagnostic exit1); zero Kani. There was one additional launcher-only refusal before Lean/GNU time. No proof, theorem, axiom, implementation, security contract or LOG edit was made. No full manifest, Rust build, SBF rebuild, native timing suite or unrelated regression was run. This task stops at the completed mechanical audit; the unused10 Lean slots are not claimed exhausted.

| Env-J ID / helper | Exit | Wall | Peak RSS KiB | Swap | Axioms result |
|---|---:|---|---:|---:|---|
|20000 / Statement admission | no compiler | unavailable | unavailable | unavailable | N/A: unrelated vanished cgroup before GNU time/Lean |
|20001 / Statement (maximally explicit diagnostic) |0|2.87s|4,211,204|0|7 existing theorem reports, standard three only |
|20002 / Readable |0|1.92s|4,211,488|0|7 existing theorem reports, standard three only |
|20003 / Fields (missing E1/E2 imports, rejected) |1|1.63s|4,198,924|0|N/A: print-only helper; no theorem declarations |
|20004 / FieldsComplete |0|1.72s|4,250,072|0|N/A: printed definitions/structures only |
|20005 / Consumers |0|1.71s|4,210,520|0|Existing privacy_headline_deployed: [propext, Classical.choice, Quot.sound] |

[receipts.json](../evidence/privacy-ledger-20261026/receipts.json) retains exact target/command, helper SHA256, actual source-stage revision plus dirty-helper qualification, exit/wall/RSS/swap, full captured axioms and errors. [admissions.json](../evidence/privacy-ledger-20261026/admissions.json) retains each reservation/barrier result and actual scope limits. The successful scopes used-M7000, MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64, one scope at a time. The documented launcher path lacked `/tools/`; a pre-existing compliant private launcher was read and copied to this job’s host directory with **only the authorized assigned-ID-range extension**, preserved in launcher-before.sh.txt and launcher-range-only.diff. No shared launcher/barrier code or proved module was altered. The existing launcher’s admission output directory is retained; no source in a sibling host workspace was edited.

20000 failed on FileNotFoundError for another vanished scope, with this job’s actual6G/8G/zero-swap/64-task limits visible. More than30s elapsed before the single permitted retry20001. Neither the compiler nor GNU time ran on20000; no missing metric is reconstructed. The second launcher invocation included the recorded direct dependency fingerprint because the first launcher had already entered its sent ledger; no failed Lean compilation was rerun unchanged. 20003’s replacement adds only the missing imports and the requested TrustedStd field print. No memory failure or cap increase occurred.

The readable root, fixed-admitted headline, builder_premises, caller_law, budgets, fibres and exhaustion audits all report only the three accepted standard axioms. Named external trust laws here are hypotheses/contracts for later deployed instances, not new Lean axioms added by this audit. The optional Formatter axiom is not in these accepted reports. [host-postrun-pins.json](../evidence/privacy-ledger-20261026/host-postrun-pins.json) records798 project modules’ source/object hashes and environment/tool hashes by read-only import traversal. All31 retained input-revision source snapshots match the corresponding host sources in [source-host-comparison.json](../evidence/privacy-ledger-20261026/source-host-comparison.json). These hashes were captured **after** the focused jobs, and are not a claim that every cached dependency was rebuilt or coherent with its dependents. The final release replay/axioms/instance-binding rows remain P.

The mechanical bookkeeping validator checks unique contiguous IDs, classes/owners/totals, every evidence reference, source/helper hashes, standard-axiom reports,35-of99 callback overlap,41+16 native-cut rows,14 trace-table rows, print-only helpers and allowed changed paths. It is not a semantic proof of the ledger or a native verification gate. Its result is in [validation-summary.json](../evidence/privacy-ledger-20261026/validation-summary.json).

LOG consistency notes (LOG left unchanged):

- **Two D190–D192 series:** D190 entropy obstruction(24 October10:55), D191 effect packet(24 October11:29), D192 entropy preflight(24 October) coexist with D190 lead resumption(25 October13:05), D191 candidate divergence(26 October), D192 barrier correction(26 October). Date/title are required to resolve citations. This ledger’s rebase/divergence D191 means the26 October entry; its old pure entropy obstruction means the24 October entry.
- **Historical counts are scoped, not contradictory completion certificates:** the26 October D19174/262 source count is an older rw checkpoint. Latest retained P6 callbacks and dictionary163/262 belong to different selectors/branches. No checked merged dictionary or root refinement is provided by adding their counts.
- **ELF identities evolve by adoption:** D162’s dfc2a91a…/fb2fc048…, D163/v2’s40dc7574…/12cb0bc2…, and current f8c0ec72…/63ad3e9c… refer to different release snapshots. v2’s old match cannot settle the rebased candidate’s current three-ELF gate. The current Pool pin remains121f3e29….
- **Nonce model history:** D52.3’s private mask nonce and the old96-byte secret triple are historical; D162 selects public proof-account nonce with two private32-byte seeds. E1’s64-byte specialization is the relevant boundary. No secret-nonce collision charge or arbitrary ledger cap is silently reintroduced.
- **Simulator contract supersession:** D44.3’s old Rust G-sim deliverable must be read with D185: the endpoint compares to mathematical simE. No proof of a deployed Rust simulator is invented as an extra endpoint premise. Complete real observable bytes, rejected attempts and side channels are still required under D159/D166.
- **L1/model acceptance is not native closure:** D163 explicitly keeps native producer/joint history/equal-circle/query-abort/part47 composition open. D166’s simulatable-trace route leaves challenge/private-coin cost laws required; historical field-kernel equivalence does not replace them. The leaf report’s seven small passing scopes and generic coupling do not prove the common full raw-input law.
- **D188 extraction trust is already accepted:** for actually extracted code, Rust-to-extraction correspondence belongs to AeneasExtraction; do not add a redundant blanket native=extracted proof gate. Non-extracted callback/wrapper contracts, source/model composition, opaque carrier/effect semantics and release artifact association still require their stated jobs.

Before/after: the target statement and every hypothesis are byte-unchanged. Premises removed0, added0, weakened0; new ledger rows only expose existing assumptions, carrier/domain restrictions, model facts and deployment requirements. No shipped-source contradiction was proved. No keys/accounts/funds were accessed, created or cleaned up; no push or merge. Next concrete deliverable: discharge the supplied complete proof/audit data equation and native effect/entropy transport, instantiate PrefixContract/BodyContract, and construct the SAME real RunJoin with both exact marginals and full observable agreement; pv-l2-sim, pv-rebase and pv-client must supply their named rows before one final coherent release replay. **Privacy target not yet established.**

Capacity-error relaunch 1 re-read the rules, reference ledger and retained receipts, then reran the bookkeeping validator with no further Lean or Kani invocation. The receipt scraper now recognizes actual Lean diagnostics rather than printed names such as `modelError` and constructors such as `Except.error`; raw transcripts and compiler outcomes are unchanged. Five Lean invocations remain used, ten unused. See [resume-1.json](../evidence/privacy-ledger-20261026/resume-1.json).


## Recount 2026-10-26 (B)

**Privacy target not established. This mechanical recount changes no endpoint premise, theorem, implementation, observer, simulator or bad event.** The original rows above remain intact. [Method and statement audit](../evidence/privacy-recount-20261026/METHOD.md), [all per-row dispositions and dependencies](../evidence/privacy-recount-20261026/ROWS.md), [machine-readable rows](../evidence/privacy-recount-20261026/rows.json), [totals](../evidence/privacy-recount-20261026/totals.json), and [immutable branch pins](../evidence/privacy-recount-20261026/pins.json) are the evidence of record.

The supplied ledger actually has **399 rows V001–V399**. Its V380 is already `TrustedStd.btree_entry_or_insert_with`. The L2 report's distinct D197 inversion obligation is added here as **V380-inversion**, an audit alias pending lead ID assignment, preserving the original V380. Total denominator is therefore **400**. No existing rows are renumbered. The exact requested V001–V380 slice and unchanged 399-row denominator are also shown below.

T/P/C classify trust/proof/diagnosis, not completion. The baseline did not provide the five requested statuses: “baseline normalized” below applies this recount's rubric to the original retained evidence. Its 87 model closures were already proved; its 145 reductions were already data fields, carried guards, overlap fields or named external hypotheses. They are not new premise removals.

| Scope | Rows | T | P | C | OPEN | REDUCED | EVIDENCED | CLOSED-ON-RESEARCH | CLOSED-ON-CANDIDATE |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Baseline normalized | 399 | 26 | 369 | 4 | 167 | 145 | 0 | 87 | 0 |
| Recount, original rows | 399 | 26 | 369 | 4 | 137 | 152 | 10 | 87 | 13 |
| Recount, V001–V380 only | 380 | 15 | 361 | 4 | 133 | 141 | 6 | 87 | 13 |
| Recount incl. V380-inversion | 400 | 26 | 370 | 4 | 138 | 152 | 10 | 87 | 13 |

CLOSED-ON-RESEARCH refers only to each original **model-scoped** statement, including its original matching-witness/public guard. Native source association remains separately OPEN. CLOSED-ON-CANDIDATE refers to exact pure extracted-source operation installations, not a deployed RunJoin. REDUCED rows retain their named fields; mere packaging into PV_L1/PV_L2/PV_RunJoin structures does not earn reduction. EVIDENCED rows retain universal/native/adoption obligations. The full row table records both scopes and residuals.

Per-row status changes since the normalized baseline (every other original row is unchanged):

| Row | Before → after | Basis / retained limitation |
|---|---|---|
| V046 | OPEN → EVIDENCED | Chosen existing R1Adv carrier inhabited; no theorem Nonempty rust.Adversary for arbitrary free rust. Native carrier identification retained in V045. |
| V047 | OPEN → EVIDENCED | Two mathematical fixture fibres proved, sentinel discharged; native chosen-public/byte associations still explicit. Arbitrary x nonemptiness NOT proved. |
| V173 | OPEN → REDUCED | This source callback is irrelevant to the complete extracted caller. Does NOT install a generic native operation/type, which is the broader original row. Seven erasures include four already-selected fields absent from original open99. |
| V174 | OPEN → REDUCED | This source callback is irrelevant to the complete extracted caller. Does NOT install a generic native operation/type, which is the broader original row. Seven erasures include four already-selected fields absent from original open99. |
| V188 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V189 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V190 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V191 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V192 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V193 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V194 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V196 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V200 | OPEN → REDUCED | rw candidate supplies fibre source callback; inherited std/native-table interpretation and SAME-selector/native association remain. Not added to dictionary sibling selector by arithmetic on counts. |
| V207 | OPEN → REDUCED | This source callback is irrelevant to the complete extracted caller. Does NOT install a generic native operation/type, which is the broader original row. Seven erasures include four already-selected fields absent from original open99. |
| V248 | OPEN → REDUCED | rw candidate supplies clone source callback; inherited std/native-table interpretation and SAME-selector/native association remain. Not added to dictionary sibling selector by arithmetic on counts. |
| V250 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V251 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V252 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V253 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V255 | OPEN → REDUCED | rw candidate supplies trace-value source callback; inherited std/native-table interpretation and SAME-selector/native association remain. Not added to dictionary sibling selector by arithmetic on counts. |
| V262 | OPEN → REDUCED | rw candidate supplies all-variant coefficients source callback; inherited std/native-table interpretation and SAME-selector/native association remain. Not added to dictionary sibling selector by arithmetic on counts. |
| V266 | OPEN → CLOSED-ON-CANDIDATE | Exact pure extracted body installed for arbitrary base/ops; complete Result including failures retained. Inspected body has no missing external callback. D188 extraction boundary retained; no cost/native RunJoin conclusion. |
| V341 | OPEN → EVIDENCED | Later candidate build at 3f9177b6477a8ae91d028139be2a9c555fc300e7 matches exact required ELF SHA and size; supersedes initial gate-status STOP. Measurement, no native proof. |
| V342 | OPEN → EVIDENCED | Later candidate build at 3f9177b6477a8ae91d028139be2a9c555fc300e7 matches exact required ELF SHA and size; supersedes initial gate-status STOP. Measurement, no native proof. |
| V343 | OPEN → EVIDENCED | Later candidate build at 3f9177b6477a8ae91d028139be2a9c555fc300e7 matches exact required ELF SHA and size; supersedes initial gate-status STOP. Measurement, no native proof. |
| V372 | OPEN → EVIDENCED | Research evidence executable/compiler/flags/CPU pinned, DOITM supported but disabled; not the adopted final release binary. |
| V392 | OPEN → EVIDENCED | Merged selected64 operational source and retained-key/attempt mapping/lifecycle tests plus four pinned-ELF runtime fixtures supplied. Universal event/effect laws and owner final client bundle adoption remain V045/V167/V396. |
| V393 | OPEN → EVIDENCED | Merged selected64 operational source and retained-key/attempt mapping/lifecycle tests plus four pinned-ELF runtime fixtures supplied. Universal event/effect laws and owner final client bundle adoption remain V045/V167/V396. |
| V394 | OPEN → EVIDENCED | Merged selected64 operational source and retained-key/attempt mapping/lifecycle tests plus four pinned-ELF runtime fixtures supplied. Universal event/effect laws and owner final client bundle adoption remain V045/V167/V396. |
| V395 | OPEN → EVIDENCED | Merged selected64 operational source and retained-key/attempt mapping/lifecycle tests plus four pinned-ELF runtime fixtures supplied. Universal event/effect laws and owner final client bundle adoption remain V045/V167/V396. |
| V380-inversion | NOT-IN-BASELINE → OPEN | Owner inversion zero-boundary decision required. Also depends on actual native reached-call/slot enumeration and SAME headline coupling; classify c by owner-first precedence. LogUp nonzero theorem is partial only. |

The thirteen candidate closures are the dictionary branch's op37/40/41/43/44/49/50/60/235/236/239/240/260 installation equations. Their actual bodies have no missing external callback; J20701 reports standard axioms for each. The same final selector composes with the complete seven-field source erasure. The original off-route op16/18/85 rows are REDUCED rather than called generic native installations. rw's op78/231/247/255 source progress retains native/library association and is not silently installed into the dictionary sibling. No candidate proof removes V036–V038, V045 or the actual whole proof/audit/native-effects association.

The later rebase comparison files supersede its initial gate-status STOP: all three required ELF identities pass on candidate source 3f9177b6477a8ae91d028139be2a9c555fc300e7. Both fixed fixtures match. Its single 13.078/13.872-second observations are not median timing gates. V047 has two proved mathematical fixture fibres, with two explicit native-public Association fields retained; arbitrary-x non-vacuity is not claimed. V046's chosen observer carrier is inhabited, not every arbitrary rust.Adversary. Client source/fixture evidence is on research, with final bundle adoption/live publication remaining V396. V372 pins the L3 evidence executable only.

For **every OPEN row**, the per-row table gives one primary dependency bucket and its reason. Owner-first precedence is used where an owner decision and native interpretation are both missing. These are whole-row completion dependencies, not an instruction to delay useful component work. REDUCED/EVIDENCED residual obligations and overlap aliases are not counted as independent OPEN gates.

| OPEN dependency | Original 399 | With inversion | Exact interpretation |
|---|---:|---:|---|
| (a) independent source obligation | 79 | 79 | Can complete before the full native interpreter/RunJoin; may depend on other source lemmas |
| (b) actual native refinement/interpretation | 51 | 51 | Requires extracted deployed caller/carrier/world/observable association feeding conjunct 1 / V038 |
| (c) owner decision | 7 | 8 | Named platform/domain/quiet-host/client adoption decision; secondary native dependencies retained |
| Total OPEN | 137 | 138 | No independent-gate or probability interpretation |

Owner rows: V344/V345 quiet-host timing barrier; V370 pinned compiler trust acceptance; V371 DOITM/CPU latency; V373 inversion zero-boundary/call-site audit policy; V374 quiet-host dudect barrier; V396 client signer/storage/bundle pin; added V380-inversion zero-boundary decision **and** native reached-call enumeration. No authorization to change CPU mode, protocol or resource policy is inferred.

All five L1 rows and all eighteen inherited L2 rows remain OPEN in (b). The added inversion obligation is OPEN in (c), with its native dependency also recorded. PV_L1_Premises/PV_L2_Premises organize uninstantiated fields; erasure theorems, references and partial LogUp nonzero results do not prove a complete native observable law on the headline coupling. More generic L2 wrappers alone cannot close these rows before native interpretation.

**Single most valuable next non-native-dependent row: V164**, complete current shipped compression ↔ owned indexed/list reference correspondence, preserving full Result/failure/divergence, arbitrary slices and the final multiplication/power update. The reference/list substep is already proved; shipped/reference correspondence remains. This is an independent source equation feeding the complete proof/audit body, not a substitute for V038.

Validation: zero new Lean invocations (0/15), zero Kani (0 allowed), no new proof/theorem/helper module, no host run or regression replay. Existing standard-axiom/source/fixture receipts were inspected and reused. Snapshot Lean sources are inert `.lean.txt` audit copies, not new compilable modules. Mechanical validation checks 400 unique audit keys, original-row preservation, class/status/bucket totals, exact candidate-closure axiom lines, source hashes against pinned git objects, and allowed changed paths. No root or sibling worktree was edited; no merge, push, wallet/key/fund operation or implementation edit. Premises removed/added/weakened by this recount: **0/0/0**.


## Recount 2 2026-10-26 (B)

**Privacy target not established.** All 400 inherited obligations have been re-derived against pinned research and unmerged branch statements. No endpoint premise, proof, implementation, observer, simulator or bad event changed. Original rows and Recount 1 remain intact. [Every row and OPEN dependency](../evidence/privacy-recount-20261026/ROWS2.md), [statement method and LOG corrections](../evidence/privacy-recount-20261026/recount2/METHOD2.md), [immutable pins](../evidence/privacy-recount-20261026/recount2/pins.json), [machine-readable rows](../evidence/privacy-recount-20261026/recount2/rows2.json), [totals](../evidence/privacy-recount-20261026/recount2/totals2.json), and [15 focused Lean receipts](../evidence/privacy-recount-20261026/recount2/receipts.json) are the evidence of record.

The same 400 comparison is separate from three newly explicit rows: V400 OS-entropy-failure model coverage (C/T-suspect, OPEN); V401 fixture byte equality and V402 corrected 1000-pair differential (P, EVIDENCED). The latter two were not distinct original rows and overlap V340/V399; they are measured deliverables, not extra universal gates. V380 and V380-inversion retain their original distinct identities.

|Inventory / status|Recount 1|Recount 2 same 400|Recount 2 incl. new rows|
|---|---:|---:|---:|
|Rows|400|400|403|
|T|26|26|26|
|P|370|370|372|
|C|4|4|5|
|OPEN|138|109|110|
|REDUCED|152|154|154|
|EVIDENCED|10|10|12|
|CLOSED-ON-RESEARCH|87|87|87|
|CLOSED-ON-CANDIDATE|13|40|40|

CLOSED-ON-CANDIDATE credits complete extracted source-value equations under D188, including arbitrary inputs and complete Result. It does not adopt or combine sibling selectors, prove native effects or close the endpoint. REDUCED retains all named fields and free-instance obligations. The endpoint record earns the requested REDUCED contract disposition only: runtime/boundary 2→2, fields 8→8; no field was discharged. V036/V037 stay OPEN for the SAME actual deployed coupling. V152–V154 remain OPEN despite canonical source-stage progress.

Per-row status changes since Recount 1 (all other inherited statuses unchanged):

|Row|Recount 1 → recount 2|Exact basis / retained limit|
|---|---|---|
|V038|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `disclosed_V038`, `observerOracle_V038`; frozen Runtime/Boundary still missing.|
|V045|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `source_V045`; frozen Runtime/Boundary still missing.|
|V169|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_TakeSource.op3_source`; complete extracted source equation. Native composition remains V165–V167.|
|V197|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op71Source.op71_source`; complete extracted source equation. Native composition remains V165–V167.|
|V198|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op72Source.op72_source`; complete extracted source equation. Native composition remains V165–V167.|
|V199|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op77Source.op77_source`; complete extracted source equation. Native composition remains V165–V167.|
|V200|REDUCED → CLOSED-ON-CANDIDATE|`R1Z.PDict_RemainingDictionary231.op78_installed`; complete extracted source equation. Native composition remains V165–V167.|
|V202|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op80Source.op80_source`; complete extracted source equation. Native composition remains V165–V167.|
|V203|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op81Source.op81_source`; complete extracted source equation. Native composition remains V165–V167.|
|V204|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op82Source.op82_source`; complete extracted source equation. Native composition remains V165–V167.|
|V205|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op83Source.op83_source`; complete extracted source equation. Native composition remains V165–V167.|
|V206|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op84Source.op84_source`; complete extracted source equation. Native composition remains V165–V167.|
|V208|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op86Source.op86_source`; complete extracted source equation. Native composition remains V165–V167.|
|V209|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op100Source.op100_source`; complete extracted source equation. Native composition remains V165–V167.|
|V210|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op101Source.op101_source`; complete extracted source equation. Native composition remains V165–V167.|
|V211|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op105Source.op105_source`; complete extracted source equation. Native composition remains V165–V167.|
|V212|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op107Source.op107_source`; complete extracted source equation. Native composition remains V165–V167.|
|V213|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op109Source.op109_source`; complete extracted source equation. Native composition remains V165–V167.|
|V214|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op110Source.op110_source`; complete extracted source equation. Native composition remains V165–V167.|
|V215|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op111Source.op111_source`; complete extracted source equation. Native composition remains V165–V167.|
|V216|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op114Source.op114_source`; complete extracted source equation. Native composition remains V165–V167.|
|V218|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op118Source.op118_source`; complete extracted source equation. Native composition remains V165–V167.|
|V223|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op127Source.op127_source`; complete extracted source equation. Native composition remains V165–V167.|
|V224|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op128Source.op128_source`; complete extracted source equation. Native composition remains V165–V167.|
|V226|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op130Source.op130_source`; complete extracted source equation. Native composition remains V165–V167.|
|V227|OPEN → CLOSED-ON-CANDIDATE|`R1Z.PV_CB_Op131Source.op131_source`; complete extracted source equation. Native composition remains V165–V167.|
|V248|REDUCED → CLOSED-ON-CANDIDATE|`R1Z.PDict_RemainingDictionary231.op231_installed`; complete extracted source equation. Native composition remains V165–V167.|
|V255|REDUCED → CLOSED-ON-CANDIDATE|`R1Z.PV_TraceValueInstall.source`; complete extracted source equation. Native composition remains V165–V167.|
|V262|REDUCED → CLOSED-ON-CANDIDATE|`R1Z.PV_ProverRwP7CoefficientsInstall.source`; complete extracted source equation. Native composition remains V165–V167.|
|V336|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `native_fill_V336`; frozen Runtime/Boundary still missing.|
|V337|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `native_ledger_V337`; frozen Runtime/Boundary still missing.|
|V338|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `byte_blind_V338`; frozen Runtime/Boundary still missing.|
|V339|OPEN → REDUCED|`PV_RunJoin_Endpoint.PV_RunJoin_Premises`: `kernels_V339`; frozen Runtime/Boundary still missing.|

These 27 candidate closures are 23 newly committed PV_CB source equations, V200/V248 dictionary fibre/clone equations, and V255/V262 rw source callbacks (op247 counted once even though dictionary also supplies it). D208's earlier 30 value interpretations alone and seven sibling-reuse notes are not closures. Remaining source rewrites/reference policies and bounded Kani gates remain OPEN.

New rows (no original renumbering):

|ID / class|Statement and status|Evidence / retained obligation|
|---|---|---|
|V400 / C (T-suspect alternative)|OS entropy failure coverage: OPEN/c|Literal selected EIO fault and conditional first-draw error/model-success disagreement. Owner repair A OsAvailable trust or B public failure in both experiments, neither adopted. Concrete outside-bad coin/native decoder association remains; no witness leak proved.|
|V401 / P|Fixed-coin fixture byte equality: EVIDENCED|Pinned control/candidate transfer and withdrawal proof/public/status/attempt/callback/audit equality. Does not rebind universal proofs or establish arbitrary-x fibres.|
|V402 / P|Corrected1000-pair differential: EVIDENCED|v3 cohort 1000/1000, 600 successful proof pairs, 100 rejected-prefix pairs (within the successful cohort), 400 error tapes; four full oracle-stream comparisons. Invalidated v2 pressure mismatch retained; no universal trace law inferred.|

V341–V343 remain EVIDENCED: all three candidate/control ELF pins and sizes match release requirements. V344/V345 remain OPEN: no qualified quiet median for either source (n=0), no absolute/relative timing verdict. V372 remains scoped platform evidence; DOITM disabled. V374 has no valid final timing verdict. V340/V346/V397–V399 retain proof rebinding and coherent release replay/axioms/association.

For every OPEN row, ROWS2.md gives its primary bucket and reason, with owner-first precedence where native work is also needed. REDUCED/EVIDENCED residuals remain explicit and are not counted as resolved native work.

|OPEN dependency|Recount 1|Recount 2 same 400|Recount 2 all 403|Change all rows|
|---|---:|---:|---:|---:|
|(a) independent source obligation|79|51|51|−28|
|(b) native extracted deployed caller / V038 / V165–V167|51|50|50|−1|
|(c) owner decision|8|8|9|+1|
|Total OPEN|138|109|110|−28|

Bucket reconciliation: 23 a callbacks close; V221/V222/V249/V263/V267 move a→b because actual erasure/fence, Instant, worker/panic and filesystem world effects require the native interpreter; six b rows become explicit REDUCED contracts; V400 adds one c row. The four pre-existing REDUCED callbacks become candidate closures and do not affect OPEN buckets. The b reduction is contract exposure, not native premise removal.

Owner decisions: V344/V345 quiet-host/Docker-cap scheduling; V370 compiler trust; V371 DOITM/CPU latency; V373/V380-inversion inversion zero-boundary/reached-call policy; V374 quiet L3 measurement; V396 client bundle/signing/storage/publication; V400 OS-failure repair A/B. No authorization to alter caps, CPU mode, protocol, model, trust or publication is inferred. All L1/L2 whole native rows remain OPEN/b; inversion remains OPEN/c.

**Corrections to lead claims (LOG left intact):** D203's “V269 reduced” is unsupported for the whole Formatter/type27 row: fallible store transport is not native Formatter sink/value/state association; V269 remains OPEN and native types remain26/28. D199's V047 “discharged for shipped statements” supports mathematical fixture fibres, not CLOSED for the arbitrary-x/native ledger row; V047 remains EVIDENCED. D201's “29 left OPEN” is a counting error:7+10+13=30 and original 399 OPEN167→137, then inversion adds one. D204's concrete-runtime claim was already corrected by D205; runtime/boundary remain parameters. D206's categorical outside-model/outside-bad description exceeds the exact conditional theorem, which still assumes fault schedule/decoder, model firstGood success and old/seed/fuel safety; no concrete outside-bad counterexample or privacy attack is constructed. The EIO fault/model-gap escalation is supported as V400 C/T-suspect. D196/D197 scoped evidence, D198/D200/D202 OPEN L1/L2, D207 two supplied callbacks, and D208's historical zero closures stand. Later CB source equations are new evidence, not retroactive credit to its value equations.

**Most valuable independent next row: V164**, the complete shipped arity16 compression ↔ owned indexed/list reference equation, arbitrary slices and every Result/failure/divergence branch including the final multiplication/power update. Reference/list/primitive substeps are available; shipped correspondence remains absent and feeds V163.

Validation: 15/15 Lean compiler invocations (Env-J24300–24314), 0 Kani, 13 exit 0 and 2 recorded diagnostic failures. All accepted printed axioms are standard only; exact source revisions, commands, wall/RSS/swap and full errors/axioms are retained. Every run used -M7000, MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, standing TasksMax 128, one scope at a time. No admission refusal or cap change. The endpoint helper saw an older shared object without uniform_V037; the OS helper lacked a dependency object. Neither was rerun, repaired or reported passing. Pinned original branch receipts support the source inspection; these cached checks are not a coherent release replay.

|Env-J / helper|Exit|Wall|Peak RSS KiB|Swap|
|---|---:|---|---:|---:|
|24300 / Callbacks1|0|0:02.40|4259800|0|
|24301 / Callbacks2|0|0:01.89|4269144|0|
|24302 / Callbacks3|0|0:01.82|4268940|0|
|24303 / Callbacks4|0|0:02.17|4264876|0|
|24304 / Callbacks5|0|0:01.86|4267532|0|
|24305 / Callbacks6|0|0:01.81|4269552|0|
|24306 / Callbacks7|0|0:02.28|4263036|0|
|24307 / Callbacks8|0|0:01.93|4269192|0|
|24308 / Dictionary|0|0:02.00|4280548|0|
|24309 / Endpoint|1|0:03.55|4209060|0|
|24310 / OsFailure|1|0:00.74|1295992|0|
|24311 / SourceIdentification|0|0:02.40|4079152|0|
|24312 / Rw|0|0:02.26|4273396|0|
|24313 / Model|0|0:02.83|4196596|0|
|24314 / Trust|0|0:02.28|4223436|0|

No new theorem/proof, runtime experiment, Kani/Rust/SBF build, timing suite or full manifest replay. Mechanical validation checks all 403 unique rows, preserved 400 statements/classes, bucket/status sums, exact git snapshots, helper-only commands and 15 receipts. No root/sibling worktree, soundness file, implementation, key/account/fund, push or merge operation. Premises removed/added/weakened: **0/0/0**. Stop: every row reviewed and all 15 statement-check slots used.


## Recount 3 2026-10-27 (B)

**Target not yet established.** This statement/dependency audit removes no
endpoint premise. The original ledger rows and both previous recounts remain
intact. [Every row, dependency and import disposition](../evidence/privacy-recount-20261026/ROWS3.md),
[method and corrections to D209–D235](../evidence/privacy-recount-20261026/recount3/METHOD3.md),
[immutable branch pins](../evidence/privacy-recount-20261026/recount3/pins.json),
[machine-readable rows](../evidence/privacy-recount-20261026/recount3/rows3.json),
[import chains](../evidence/privacy-recount-20261026/recount3/import-closures.json),
and [20 statement-check receipts](../evidence/privacy-recount-20261026/recount3/receipts.json)
are the evidence of record. No proof, theorem, implementation, observer,
simulator, bad-event definition or release pin was changed.

The denominator grows by four explicitly tracked P rows: V403 canonical M31
domain at op121 callers, V404 transfer reachability, V405 withdrawal
reachability, V406 owner adoption of the proposed three-field T. These are
slices/decisions with recorded overlaps, not four independent security gates.
**V240/op223 is V164's remaining P_source_p6; it is linked, never counted twice.**
The proposed T is not accepted trust: the original T/P/C classes stay intact.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 |
|---|---:|---:|---:|
| Rows | 400 | 403 | 407 |
| T | 26 | 26 | 26 |
| P | 370 | 372 | 376 |
| C | 4 | 5 | 5 |
| OPEN | 138 | 110 | 103 |
| REDUCED | 152 | 154 | 176 |
| EVIDENCED | 10 | 12 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 |

On the **same inherited 403 rows**, recount 3 is OPEN 99, REDUCED 176,
EVIDENCED 14, CLOSED-ON-RESEARCH 87, CLOSED-ON-CANDIDATE 27, with T/P/C
26/372/5. The four new OPEN P rows bring OPEN to 103 and P to 376.
The decrease in candidate closure labels is a correction under the requested
strict source criterion, not regression of the underlying proved equations.

There are **26 exact operation source closures**: 23 from the callback branch
and three unique CB3 rows (op120, op225, op246). op229/V246 appears on both
branches and counts once. The scoped Formatter-axiom diagnostic V270 adds
one candidate closure, giving 27. V269's original native Formatter type,
value, options, sink, failure/state/world row remains OPEN; types stay 26/28.
The original 87 research closures are model-scoped and retain their guards.

For a V169–V267 candidate source closure, the complete extracted Result
equation must be supplied: an installed equation or bounded Kani gate alone
is insufficient. Seventeen former installed/value closures and the older
op81/V203 selected heap interpretation therefore return to REDUCED.
The stronger fresh Exact equations replace several partial source labels
already counted in recount 2, so they are not five additional ledger rows.

| CLOSED-ON-CANDIDATE import disposition | Count |
|---|---:|
| In research headline closure | 0 |
| In candidate refinement_of_data consumer closure | 17 |
| In neither | 10 |

The ten in neither are V197, V206, V209, V210, V212, V213, V214, V218, V219
and V270. Nine are source laws whose exact current theorem is absent from the
consumer import paths; V270 is an axiom-audit property with no imported
closure theorem. Among the 26 operation source rows alone: 0 research,
17 candidate, 9 neither. Import membership is not a proof of the caller's
whole-data premise. All 407 row dispositions are separately listed as
research 160 / candidate 133 / neither 114; for non-closure rows this records
only defining-source membership, not discharge.

The consumer roots are PV_Join_AggregateCaller, PV_Join_PublicCaller,
ProverRw19CanonicalAuditRefinement and ProverRw18ContextData. Paths and exact
source bindings are retained; older imported partial names do not confer
credit on newer Exact laws. Missing candidate dictionary source files are
resolved explicitly from the pinned dictionary branch for graph analysis;
this is not a coherent object/source replay certificate. No audit module is
used as a root to create membership.

Per-row changes since recount 2 (every other inherited status is unchanged;
all inherited rows are individually re-derived in ROWS3.md):

| Row | Recount 2 → recount 3 | Evidence / retained limit |
|---|---|---|
| V152 | OPEN → REDUCED | Source-identification interfaces and canonical source-stage laws reduce the row to five named families. words/publicCorr/admission/row_call REDUCED; compile_call OPEN. Deployed premises 5→5; reference 3. Concrete native returned compiler/carrier association is not provided. D231 merge gate blocked by stale cached object; newer resume6 additionally records a protected source replay failure, not a row counterexample. No whole deployment closure. |
| V153 | OPEN → REDUCED | Source-identification interfaces and canonical source-stage laws reduce the row to five named families. words/publicCorr/admission/row_call REDUCED; compile_call OPEN. Deployed premises 5→5; reference 3. Concrete native returned compiler/carrier association is not provided. D231 merge gate blocked by stale cached object; newer resume6 additionally records a protected source replay failure, not a row counterexample. No whole deployment closure. |
| V154 | OPEN → REDUCED | Source-identification interfaces and canonical source-stage laws reduce the row to five named families. words/publicCorr/admission/row_call REDUCED; compile_call OPEN. Deployed premises 5→5; reference 3. Concrete native returned compiler/carrier association is not provided. D231 merge gate blocked by stale cached object; newer resume6 additionally records a protected source replay failure, not a row counterexample. No whole deployment closure. |
| V164 | OPEN → REDUCED | rw18/rw20 source decomposition and concrete context identity are checked. Remaining single hypothesis P_source_p6 identifies ops.op223 with ProverRwP6CompressSource.compress under PV_CurrentScaleInstall.selected. This is V240/op223, not an extra independent row. Context identity is discharged; original shipped-helper correspondence is not. |
| V188 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V189 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V190 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V191 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V192 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V193 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V194 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V196 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V200 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V203 | CLOSED-ON-CANDIDATE → REDUCED | op81 selected heap interpretation and caller specialization exist, but the current 23/73 extracted-source inventory does not credit op81. PV_CB_Op81Source is an older selected-reference equation, not fresh extracted shipped Vec allocation source. Keep the useful caller/dictionary bridge; stricter source-closure credit withdrawn. |
| V219 | OPEN → CLOSED-ON-CANDIDATE | Complete extracted source Result equation in CB3, composed in CallbackBundle. All unrelated callbacks remain arbitrary; source/native/release joins are retained. This row is distinct from V246/op229. |
| V242 | OPEN → CLOSED-ON-CANDIDATE | Complete extracted source Result equation in CB3, composed in CallbackBundle. All unrelated callbacks remain arbitrary; source/native/release joins are retained. This row is distinct from V246/op229. |
| V246 | OPEN → CLOSED-ON-CANDIDATE | Complete extracted source Result equation for arbitrary declared inputs; nominal carrier conversions are explicit and all failure/divergence outcomes remain. D188 extraction boundary retained. Native effects, carrier/world and release association remain V165–V167. 24034.json; prior restored replay 27161.json; Direct candidate equality extraction includes M31 and verified-afterstate Eq bodies; no external function template imported. Exact pointwise dictionary law uses a proved bijective nominal record conversion (PV_CB_Op229Codec). … |
| V248 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V250 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V251 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V252 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V253 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V254 | OPEN → CLOSED-ON-CANDIDATE | Complete extracted source Result equation in CB3, composed in CallbackBundle. All unrelated callbacks remain arbitrary; source/native/release joins are retained. This row is distinct from V246/op229. |
| V255 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V262 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V266 | CLOSED-ON-CANDIDATE → REDUCED | Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation. |
| V270 | OPEN → CLOSED-ON-CANDIDATE | D219 Formatter forbidden-axiom release-blocker audit: 12,920 declarations in 321 candidate family modules and endpoint roots have only propext/Classical.choice/Quot.sound. This closes the scoped inadmissible axiom-route diagnostic, not native Formatter adequacy V269 or a coherent release replay. Original 26201/26203 audit receipts reused; 38608 could not check a separate owned-coefficient helper because its object is missing. |
| V344 | OPEN → EVIDENCED | D216 qualified quiet-host timing PASSED: transfer research/candidate medians 38.909/13.742 s, withdrawal 38.560/13.499 s; n=5 each, twenty quiet pre/post checks; candidate <15 s and <=1.10x. Fixture medians only, not universal constant-time/native refinement. Earlier invalidated windows retained. |
| V345 | OPEN → EVIDENCED | D216 qualified quiet-host timing PASSED: transfer research/candidate medians 38.909/13.742 s, withdrawal 38.560/13.499 s; n=5 each, twenty quiet pre/post checks; candidate <15 s and <=1.10x. Fixture medians only, not universal constant-time/native refinement. Earlier invalidated windows retained. |
| V403 | NOT-PREVIOUSLY-SEPARATE → OPEN | Prove every M31 reaching op121 from actual caller producers is in [0,P). Retained challenge 2^31 is noncanonical: it refutes only the unrestricted Horner replacement, not selected entry=self extraction. Producer polynomial/interpolation canonicality has later partial source lemmas; challenge semantic/update/read composition and full reached-domain invariant remain OPEN. This is a proof obligation, never new accepted trust. |
| V404 | NOT-PREVIOUSLY-SEPARATE → OPEN | Determine the actual execution-reached entries and prove any exclusion for all admitted transfer inputs. Static import/dependency paths are not execution witnesses. Universally excluded set remains empty; conditional serialization-panic prefix and op226-first-after-entry do not establish reach/admission. Distinct fixture slice of V163; no new callback inventory decrement. |
| V405 | NOT-PREVIOUSLY-SEPARATE → OPEN | Determine the actual execution-reached entries and prove any exclusion for all admitted withdrawal inputs. Static import/dependency paths are not execution witnesses. Universally excluded set remains empty; conditional serialization-panic prefix and op226-first-after-entry do not establish reach/admission. Distinct fixture slice of V163; no new callback inventory decrement. |
| V406 | NOT-PREVIOUSLY-SEPARATE → OPEN | Owner decision pending for entropy_law (E1), entropy_kernel (joint 128-draw density), observation (native outcomes/filesystem/complete observer equal extracted execution). None is equality to the security experiment. Do not silently inflate accepted T or treat conditional candidate headline as deployed closure. A/B OS-failure repair remains separate V400. |

V163 remains OPEN but moves from (a) to (b): the independent mathematical
serializer is published, while the concrete deployed-input-to-model instance
and full proof-byte/data equations are still missing. V164 is REDUCED to
P_source_p6 / V240; rw20's concrete context identity is checked. Source-ID
families words/publicCorr/admission/row_call are REDUCED, compile_call OPEN;
V152–V154 are REDUCED, never deployed closures. The merge gate remains blocked
by the stale-object/provenance issue; newer resume6 records a rejected protected
source replay failure as well. No protected source is edited here.

| OPEN dependency | Recount 2 | Recount 3, same 403 | Recount 3, all 407 | Change, all rows |
|---|---:|---:|---:|---:|
| (a) independent source obligation | 51 | 41 | 44 | -7 |
| (b) native interpretation / concrete model instance | 50 | 51 | 51 | +1 |
| (c) owner decision | 9 | 7 | 8 | -1 |
| Total OPEN | 110 | 99 | 103 | -7 |

Bucket (a) loses V152–V154, V164, V270, four unique new source closures
(V219/V242/V246/V254), and V163's native-dependent completion; it gains the
three new source/reachability families. Bucket (b) gains V163. Bucket (c)
loses timing rows V344/V345 after D216 and gains proposed-T adoption V406.
Owner-first rows are V370 compiler preservation, V371 DOITM/CPU latency,
V373 and V380-inversion inversion boundary, V374 Docker-cap/quiet-host dudect,
V396 client bundle pin, V400 OS-entropy-failure repair A/B, V406 exact T list.
All five L1 and eighteen inherited L2 rows remain native-dependent OPEN.
REDUCED/EVIDENCED residuals are not disguised as completed native gates.

Corrections and supported lead claims, stated plainly:

- D211/recount 2 over-credited installed/value interpretations as extracted
  source closures. The 18 affected rows are explicitly downgraded above.
- D219 closes the candidate Formatter-axiom blocker only. It does not close
  V269's full native interpretation; V270 gets the scoped diagnostic closure.
- D223 is correct: refinement_of_data has no callback-hypothesis list. Its
  ExternalFuns value, reservation and whole proof/audit data equation remain.
  The source callback inventory is **30**, not 31; selected-entry source
  correspondence is not another inventory decrement. Both fixture reached
  sets remain unresolved; universally excluded entries are **none proved**.
- D226 counts op229/V246 twice across cb/cb3: only three unique additions,
  not four. Its 40→44 / 110→106 arithmetic is unsupported as unique-row
  arithmetic; cb5 inherits that duplicated baseline.
- D235's operation-to-row labels are incorrect: op84 is V206, op105 V211,
  op107 V212, op109 V213, op118 V218. The source table's 23/73 is supported;
  these strengthen five older partial equations already counted in recount 2.
- Op51/V195 remains OPEN as requested. The newer cb5 final report claims
  arbitrary-carrier P6 coverage and a checked reference-selector wrapper;
  that claim is retained explicitly, without silently reversing the withdrawal.
- D232 supplies constructed-candidate initial/causal, while **deployed P is
  unchanged: 2→2 / 8→8 / 6→6**. T stays exactly three proposed fields:
  entropy_law, entropy_kernel, observation. Neither owner adoption nor A/B
  OS-failure repair nor deployed (P ∧ T) fixture inhabitance is supplied.
- D234's noncanonical M31 reference disagreement is retained and is **not a
  row counterexample**. The canonical-domain proof is V403; no assumption,
  raw carrier restriction on source self-equality, or shipped fix is added.
- D216's timing pass supports V344/V345 EVIDENCED (5 samples per fixture and
  binary; transfer 13.742 s, withdrawal 13.499 s candidate medians). It is not
  a universal side-channel theorem. pv-envfix repairs the environment only.

**Single most valuable independent next row: V240/op223**, exact complete
shipped/extracted-source correspondence for arbitrary slices and Result
outcomes. It is V164's last P_source_p6 and feeds V163; a reference-only
extraction or another selector equation does not finish it.

Validation: **20/20 Lean statement-check invocations**, Env-J38600–38619;
19 exit 0, one exit 1 (38608, exact missing
R1Z/PDict_OwnedCorrect262.olean). Every run records target, exit, wall, peak RSS,
swap, revision/source hash, dependency fingerprint and full axioms/errors.
All accepted axiom reports are standard only. No retry or cap/range change;
current launcher TasksMax=64, -M7000, MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax=0, one scope at a time. Missing helper object is not reported
passing or confused with D219's separately reused audit. Zero Kani, new proofs,
runtime suites, Aeneas/SBF/Rust builds or full manifest replay. No sibling/root
worktree edit, merge, push, or key/account/fund operation. Premises
removed/added/weakened: **0/0/0**. Stop: all rows re-derived, statement budget
exhausted. **Target not yet established.**

## Owner decisions 2026-10-27 (B)

The owner accepted every pending Stream B recommendation on 2026-10-27 ("agree with all your
recommendations"). Effect on this ledger:

1. **Trust list T adopted and capped.** `R1Z.PV_RunJoin_TrustItems` (codex/pv-runjoin-20261026,
   evidence/pv-runjoin6-20261026/trust-items.md) is the privacy trust list, class T, OS-kernel contract:
   `entropy_law` (E1: 64 successful getrandom bytes uniform given the complete prior context),
   `entropy_kernel` (joint density of the 128 draws), `observation` (native getrandom/file/time/worker
   outcomes, filesystem state and the complete D159 observer payload equal the extracted execution; NOT an
   equality with the security experiment). No further T field may be added: any new native fact is a P
   obligation. Every P obligation of `PV_RunJoin_TrustEndpoint.ProofObligations` remains proof work.
2. **OS-failure repair: option B adopted** (D215): the environment-failure signal becomes a public input
   to BOTH the real and the ideal experiment, the error bound unchanged; the observer stays complete. The
   recommendation was conditional on the failure event being witness-independent; that is now a P row of
   this ledger (to be proved; option A, an `OsAvailable` trust item, applies only if it fails).
3. **V371 (CPU-latency trust item).** Adopted: enable DOITM on the pinned build/prover host and accept
   V371 only in DOITM mode. Status 2026-10-27: NOT ENABLED. The host boots with Secure Boot, so the kernel
   is in lockdown integrity mode and refuses raw MSR writes (`Lockdown: wrmsr: raw MSR access is
   restricted`); IA32_ARCH_CAPABILITIES (0x10a = 0xdc9fd6b) reports DOITM support, IA32_UARCH_MISC_CTL
   (0x1b01) = 0 on every CPU. Until firmware or kernel configuration changes, V371 stays a substantive T
   item for L3.
4. **Inversion zero-boundary (V380-inversion).** Adopted as proof work: every `try_inv` operand on a
   witness-bearing path is nonzero except on an already-charged bad event; a reachable witness-dependent
   zero is a protocol-level leak to be reported, not absorbed.
5. **Docker-cap barrier.** Adopted: three over-provisioned container caps shrunk at runtime (crypto-tax
   worker 6 GiB → 2.5 GiB, LaTeX server 4 GiB → 512 MiB, crypto-tax reports 2 GiB → 512 MiB; each ≥ 2×
   its observed peak; Postgres, API and other caps unchanged); finite container caps 24,576 → 15,872 MiB.
6. **Client bundle pin.** Adopted: pin `client-pins.json` in the release ledger (Stream A's file; handed
   to Stream A).
7. **Corpus archival.** Done: the invalidated corpus-overparallel-v2 and the superseded smoke and phase
   paired outputs deleted (4,060 files, 23 GiB; sha256 manifest evidence/pv-archive-20261027/
   deleted-files.sha256); corpus-1000-002 and focused-paired-001 kept.

## Recount 4 2026-10-27 (B)

**Target not yet established.** All 407 rows have been re-derived at the immutable
[branch pins](../evidence/privacy-recount-20261026/recount4/pins.json). Original rows,
recounts 1–3 and owner decisions are intact. This is a mechanical statement/source
audit: no proof or implementation change and no endpoint premise removed, added or
weakened. [ROWS4](../evidence/privacy-recount-20261026/ROWS4.md) records every row;
[rows4.json](../evidence/privacy-recount-20261026/recount4/rows4.json) retains exact
source/definition hashes, residuals, classifications, routes and import paths.
[Method](../evidence/privacy-recount-20261026/recount4/METHOD4.md) and
[D236–D261 corrections](../evidence/privacy-recount-20261026/recount4/CORRECTIONS4.md)
define the scope of these counts.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 | Recount 4 |
|---|---:|---:|---:|---:|
| Rows | 400 | 403 | 407 | 407 |
| T | 26 | 26 | 26 | 3 |
| P | 370 | 372 | 376 | 400 |
| C | 4 | 5 | 5 | 4 |
| OPEN | 138 | 110 | 103 | 95 |
| REDUCED | 152 | 154 | 176 | 176 |
| EVIDENCED | 10 | 12 | 14 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 | 35 |

The denominator is unchanged. Eight newly credited candidate ledger scopes are
V195/op51, V177/V179/V180/V185/V186, V240/op223 and its V164 bridge; seven
were OPEN and one REDUCED. V406 owner adoption moves OPEN→REDUCED: accepted
trust is retained, not proved. Hence OPEN 103→95, candidate closures 27→35.
V164 and V240 are two ledger scopes but one callback inventory decrement.

D248 classes are applied in additional recount fields. T rows are V329
(entropy_law), V406 (the aggregate entropy_law/entropy_kernel/observation), and
the explicitly retained V371 L3 hardware item. **Three T rows do not mean three
independent fields**: V329 overlaps V406; the RunJoin record remains exactly three
fields, with no fourth field. V371 remains substantive T until DOITM is enabled.
Former native T rows are P with their unresolved residuals retained; V391
classical ROM/P1 is P (instantiate/associate the fixed ideal-oracle model; no
computational SHA proof inferred). C retains its contradictory/vacuity-suspect meaning.
V400 is now P for the adopted option-B independence obligation. Original T/P/C
values remain visible in ROWS4 and the historical rows. REDUCED is not closure.

| Candidate closure route | Ledger rows |
|---|---:|
| extraction bridge | 1 |
| extraction | 27 |
| P6 gate | 6 |
| axiom diagnostic | 1 |

There are 27 extracted operation laws (23 cb + three unique CB3 + applied op223),
six P6-gate operation laws (op51 and five CBL), one dependent extraction bridge
(V164), and the V270 axiom diagnostic. cb3 track five plus cb 23 yields 27
unique operations after op229 deduplication; adding CBL five and applied op223
gives 33 unique operation laws. No SHA/library/native/deployed closure is inferred
from supporting reference equations.

The four D256 CBL rows are **CLOSED-ON-CANDIDATE (P6 gate)**, not extraction:
owned references + no-stub bounded Kani + selected dictionary laws. PathBuf/Path
uses an explicit candidate carrier (Path=retained PathBuf), not a native borrowed/
owned layout/lifetime proof. Path gate bytes≤4, actual Vec gate length≤2, default
is loop-free. Loop-free leaves support the structural route, but bounded harnesses
remain bounded; extraction and Kani rustc differ and deployment association is
open. The ongoing CBL continuation has additionally published op28/V179, with a
two-byte UTF-8 gate and selectedString carrier; it is credited at the same explicit
P6-gate scope, not promoted to an arbitrary-length native proof or a completed
CBLib2 campaign. See the per-row qualifications.

Applied op223 publishes `PV_Op223_Source.op223_source` and `P_source_p6`.
`PV_Op223_V164.refinement` supplies that hypothesis on the selected candidate;
reservation and P_proof_bytes remain. V163 still needs the deployed model input
and full proof/audit equation. Adoption gates remain open, including final artifact/
fixture/differential/timing/release binding; the verifier helper is unchanged.

| in headline closure? | All 407 rows | Candidate closure rows |
|---|---:|---:|
| research | 160 | 0 |
| candidate | 137 | 29 |
| neither | 110 | 6 |

On the SAME 27 recount-3 closures, the wire IMPORT-CHAIN changes 0/17/10 to
**0/26/1** (research/candidate/neither), mechanically checked edge by edge.
V270 has no closing operation theorem and stays neither. The eight new closure
scopes add op51 and the two op223/bridge scopes to candidate membership; five CBL
publication laws remain neither. Thus the 35 closures split **0/29/6**. The
candidate root includes the actual wire caller definition and the applied V164
consumer; publication modules alone are not invented roots. Non-closure row
membership means defining-source presence only, not discharge.

| OPEN dependency | Recount 3 | Recount 4 | Change |
|---|---:|---:|---:|
| (a) independent source / proof / evidence | 44 | 23 | -21 |
| (b) native / RunJoin / D245 Records / V163 model | 51 | 55 | +4 |
| (c) owner action (DOITM firmware/kernel only) | 8 | 1 | -7 |
| (d) shared extraction obstruction; route(ii) candidates | 0 | 16 | +16 |
| Total OPEN | 103 | 95 | -8 |

The buckets are exclusive; every OPEN row is assigned individually in ROWS4.
D257 identifies 15 exact escaping-reference-guard operation failures, of which
applied op223 is now candidate-closed. The remaining 14 are bucket d; the
subsequent CBL op26 adapter and op31 exact-source failures add two, for **16**.
op36 concerns owned conversion adapters, not a claimed rejection theorem for
the generic std function. op253 has a separate internal shared-loan failure and
stays a; Drop-only failures and arithmetic timeouts are not silently folded into
the exact shared-guard bucket. Only op223 route(ii) is approved/applied; all other
route(ii) entries remain design candidates. Kani is not a pending arithmetic route.

Bucket b gains V370 compiler preservation, V396 client integration and
V380-inversion after D248, and op32/V183 native allocator effects. Bucket c
retains only V371: Secure Boot lockdown prevents enabling DOITM. Inversion,
disassembly, final dudect, option-B independence and client execution binding no
longer await an owner policy decision. Docker caps and the client bundle pin are
done; the release ledger pin does not prove the client execution theorem.

Source identification on research has CLEAN (h′) merge gate, 21 source cells
and publicCorr source-root closure. V152–V154 stay REDUCED: compile_call and
deployed Records/snapshot/installed compiler identification survive. RunJoin8–12
constructed P={source public binding, trace}; deployed P and record counts
2/8/6 are unchanged. D245 exact missing equation is: on the SAME fixture arguments,
`Records.call R_shipped w 600 (some recipient) change snapshot 77 =
@PV_Src_RecordDynamic.call E_shipped w 600 (some recipient) change snapshot 77`.
The shipped R_shipped extraction/identification is absent. Literal recorded
public values do not supply it, the native compiler-return equation, transition
association or fixture non-vacuity.

V380-inversion remains OPEN/P: conditional same-coin containment is in the
existing poleBad at the same attempt with P and original coupling; charge remains
`8*(4096/((2^31-1)^4-1))`. Model tail masks/order/dedup are closed; native
registry/banks/caller/Records, P-false branches and full limb/address/latency
observation remain. Option B has a checked fixed-signal statement but its
endogenous reached-failure independence/transport is open; no admitted native
counterexample or option-A selection is inferred.

Per-row changes since recount 3 (status, class, bucket or import membership;
all unchanged rows are nevertheless re-derived in ROWS4):

| Row | Status 3 → 4 | Class 3 → 4 | OPEN bucket 3 → 4 | headline membership 3 → 4 |
|---|---|---|---|---|
| V164 | REDUCED → CLOSED-ON-CANDIDATE | P → P | — → — | candidate → candidate |
| V177 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V178 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V179 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V180 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V182 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V183 | OPEN → OPEN | P → P | a → b | candidate → candidate |
| V185 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V186 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V187 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V195 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → candidate |
| V197 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V201 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V206 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V209 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V210 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V212 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V213 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V214 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V218 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V219 | CLOSED-ON-CANDIDATE → CLOSED-ON-CANDIDATE | P → P | — → — | neither → candidate |
| V228 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V229 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V231 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V234 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V235 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V236 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V237 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V238 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V239 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V240 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → candidate |
| V241 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V256 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V264 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V330 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V331 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V332 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V333 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V334 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V335 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V370 | OPEN → OPEN | T → P | c → b | neither → neither |
| V373 | OPEN → OPEN | P → P | c → a | neither → neither |
| V374 | OPEN → OPEN | P → P | c → a | neither → neither |
| V375 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V376 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V377 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V378 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V379 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V380 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V381 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V382 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V383 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V384 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V385 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V386 | REDUCED → REDUCED | T → P | — → — | candidate → candidate |
| V387 | REDUCED → REDUCED | T → P | — → — | neither → neither |
| V388 | REDUCED → REDUCED | T → P | — → — | neither → neither |
| V389 | REDUCED → REDUCED | T → P | — → — | neither → neither |
| V390 | REDUCED → REDUCED | T → P | — → — | neither → neither |
| V391 | REDUCED → REDUCED | T → P | — → — | neither → neither |
| V396 | OPEN → OPEN | P → P | c → b | neither → neither |
| V380-inversion | OPEN → OPEN | P → P | c → b | neither → neither |
| V400 | OPEN → OPEN | C → P | c → a | neither → neither |
| V406 | OPEN → REDUCED | P → T | c → — | neither → neither |

Unchanged-status material updates: V152–V154 source-ID CLEAN/publicCorr source
half; V163 rw21 serializer with D245 residual; V038/V045/V336–V339 constructed
RunJoin reductions with deployed P unchanged; V380-inversion model tail closure.

Corrections are explicit in CORRECTIONS4.md: D241/D254 wrong-source gap claims
are withdrawn by D243/D255; D236 inherits the old op229 duplicate baseline;
D256 bounded P6/native/carrier scope must be retained; D257 op36 adapters are not
the generic shipped conversion. No other assessed D236–D261 closure claim is
promoted beyond its actual statement. V270 is not native Formatter closure;
source parent cells, trust-field overlaps and fixture slices are not new callback
decrements. No existing soundness contract or target has been weakened.

Three valuable independent next rows (current bucket a): **V403**, canonical
op121 producer/domain composition; **V400**, reached-failure signal synchronization
for option B against the existing headline bad-event accounting; **V230/op134**,
exact active-row-mask shipped/source correspondence, with Lean extraction or a
structural source bridge rather than another chained-arithmetic Kani gate.
D245 selected Records is the highest shared dependency but belongs to b.

Validation: **20/20 statement-only Lean invocations**, Env-J44500–44519,
16 exit 0; four exit 1 (44501 helper namespace typo; 44510/44511 missing
PV_Op223 source/bridge objects; 44518 missing PV_Inv_GuardCoupling object).
Failed helpers are retained, not rewritten or reported passing; no unchanged
rerun. [Receipts](../evidence/privacy-recount-20261026/recount4/receipts.json)
record target, command, exit, wall, peak RSS, swap, revision/source/dependency
hashes, direct-source equality and complete axioms/errors. Successful reports
have only standard axioms. Original source-law/bridge receipts are reused and
kept distinct from these checks; missing shared objects do not negate their
private-cache proofs. No shared source was overwritten, local Lean compile,
Kani/proof/runtime/Rust/SBF build, full regression, key/fund operation, merge or
push. Resource caps remain 6G/8G/no swap/-M7000, one scope at a time.
Stop: every row re-derived and the statement budget exhausted. **Target not yet
established.**

## Recount 5 2026-10-27 (B)

**Target not yet established.** All 407 rows are re-derived at immutable
[branch pins](../evidence/privacy-recount-20261026/recount5/pins.json), with
the candidate fixed to **0c9dc9a4cc**. Original rows, recounts 1–4 and the
owner-decisions section remain intact. [ROWS5](../evidence/privacy-recount-20261026/ROWS5.md)
has the same per-row columns, exact residuals, a/b/c/d buckets and the headline
membership column. [rows5.json](../evidence/privacy-recount-20261026/recount5/rows5.json)
retains the historical fields and current derivations, definition hashes and
import paths. This is a source/statement audit, not proof work or adoption.
Endpoint premises removed/added/weakened: **0/0/0**.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 | Recount 4 | Recount 5 |
|---|---:|---:|---:|---:|---:|
| Rows | 400 | 403 | 407 | 407 | 407 |
| T | 26 | 26 | 26 | 3 | 3 |
| P | 370 | 372 | 376 | 400 | 400 |
| C | 4 | 5 | 5 | 4 | 4 |
| OPEN | 138 | 110 | 103 | 95 | 93 |
| REDUCED | 152 | 154 | 176 | 176 | 176 |
| EVIDENCED | 10 | 12 | 14 | 14 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 | 35 | 37 |

Only V181/op30 and V182/op31 change status, OPEN→CLOSED-ON-CANDIDATE
(P6 gate). Seven library laws now coexist in PV_CBL_AppendBundle. New op30
native link is capacity/content for n≤4 with an empty-byte String adapter;
op31 is valid UTF-8 initial length 2 plus tail length 1, with checked byte/UTF-8
transport. Their allocation/world effects, source-image assumptions, separate
extraction/Kani toolchains and unbounded deployed association remain explicit.
The five earlier library bounds and op51 arbitrary-u32 carrier qualification
are retained. No generic SHA wrapper row is closed by the owned soft digest.

| Candidate closure route | Recount 4 | Recount 5 |
|---|---:|---:|
| extraction | 27 | 27 |
| extraction bridge | 1 | 1 |
| P6 gate | 6 | 8 |
| axiom diagnostic | 1 | 1 |

There are 35 unique operation-law scopes (27 extracted, 8 P6), plus V164’s
dependent bridge and V270’s axiom diagnostic. op229 is counted once. V164 and
V240 remain two ledger scopes and one callback decrement. At the requested
candidate, applied op223 extraction is present and V164 has exactly
**{reservation, P_proof_bytes}**; this was already credited in recount4 and
is not counted again. Pre-rebase ELF/fixture/1,000-pair evidence does not prove
integrated candidate validation or the final timing/adoption gate.

| in headline closure? | Recount 4 all rows | Recount 5 all rows | Recount 4 candidate closures | Recount 5 candidate closures |
|---|---:|---:|---:|---:|
| research | 160 | 160 | 0 | 0 |
| candidate | 137 | 135 | 29 | 29 |
| neither | 110 | 112 | 6 | 8 |

Actual consumer import graphs and identical law bodies are checked, including
the applied V164 root on 0c9dc9a4cc and the historical wire caller. Publication
or audit modules are not invented consumer roots. Defining-source membership
for OPEN/REDUCED rows is not discharge; no candidate law is promoted into the
research headline. The original wire set remains 0/26/1.

| OPEN dependency | Recount 4 | Recount 5 | Change |
|---|---:|---:|---:|
| (a) independent source/proof/evidence | 23 | 10 | -13 |
| (b) native/RunJoin/Records/model instance | 55 | 55 | +0 |
| (c) owner action before final evidence | 1 | 6 | +5 |
| (d) exact shared escaping-reference obstruction | 16 | 22 | +6 |

Buckets are exclusive, with exact d first, then unresolved owner action c,
then native association b, otherwise independent work a. V182 leaves d and
V181 leaves a through P6. Exact new shared-guard failures move V230, V243–V245,
V247, V257 and V258 from a to d. Drop-only/internal failures and unmeasured
successors are separately described, not inflated into that count. The original
route(ii) snapshot is 4 accepted emissions/16 refused/7 unmeasured; interim
Drop-free probes are not generic equivalence or source-law closure.

New owner-first dependencies are V370 (client toolchain), V373/V374 (selected
release recipe/final binary), V396 (client build/scope), and V232 (actual SHA-NI
semantics versus soft route), alongside V371 DOITM. These overlap decisions,
not six independent trust fields. The capped RunJoin T is unchanged: exactly
entropy_law, entropy_kernel, observation. V329 overlaps aggregate V406; V371
is the retained hardware exception. SHA-NI semantics is not silently added to T.
V400 and V403 move a→b: off-existing-bad-event option-B and canonical producer
facts now expose the native failure-metadata/prefix/caller associations.

**Side-channel classification.** N1 is fixed in the inspected candidate CT path
under the recommended recipe (ct-host-prover on, insecure-spend-fixture off),
pending release adoption/toolchain and full transitive audit. N2–N6 remain L2
native correctness/trace obligations; ideal rejection/count/uniformity, cursor
and guard algebra do not discharge E1/E2/RunJoin/simE associations. N7 is a
**key-custody side channel**, because the private boundary input is each signing
keypair’s seed, while note witnesses are constructed inside the fixture harness.
It is recorded separately in [CUSTODY5](../evidence/privacy-recount-20261026/recount5/CUSTODY5.md),
not added to the privacy denominator. The raw-pipe/fixed-copy patch is prepared
only; Python parsing/storage, OS I/O, validation and signing remain residuals.

RunJoin records repairs remain documented and ELF-checked, but latest repair 14
still fails internally: **R_shipped is not established**. Both fixture/general
record identification, native compiler-return, selected transition, deployed public
binding and P∧T non-vacuity remain. Constructed P={source public binding, trace},
deployed P OPEN, record counts 2/8/6 unchanged. Research inversion rounds 1–3
remain conditional same-coin containment in existing poleBad, not native closure.
op134 has a complete reference side and an exact shipped extraction refusal.
Batch1 repaired the op254 release-byte mismatch using a prover-local copy;
three rebuilt ELF pins now match, but source laws/shift/pole/fixture gates are
not complete at its pin. No V247/V261/V264 closure follows.

Research’s dry replay is coherent: 672 project modules, 537 reused/135 compiled,
no project proof failure; 3,905 theorem queries have standard axiom union. This
is not the final adopted endpoint/instance/release replay: V397/V398 stay OPEN.
The candidate rebase and proof-account route are evidenced, but final compiler,
observer and deployment/certificate associations remain.

[Corrections D262–D284](../evidence/privacy-recount-20261026/recount5/CORRECTIONS5.md)
audit every LOG entry. Material corrections: D272 N7 is custody (D284); D273’s
soft-SHA gate failure is projected, not an actual whole-prover gate result, and
its census is fixture-scoped; CB9’s op259 “already proved” is unsupported by
the PREPARED/pending sibling source, so V265 remains OPEN. D280/D281 in-place
weights claims are superseded by D282/ruling(l), including the default
programs/r1-cost-probe module gate. D282’s batch1 pin failure was subsequently
repaired; no source-law credit follows. Historical recount4 counts remain intact.

Per-row status/class/bucket/headline changes (all other rows nevertheless re-read):

| Row | Status 4 → 5 | Class 4 → 5 | OPEN bucket 4 → 5 | headline membership 4 → 5 |
|---|---|---|---|---|
| V181 | OPEN → CLOSED-ON-CANDIDATE | P → P | a → — | candidate → neither |
| V182 | OPEN → CLOSED-ON-CANDIDATE | P → P | d → — | candidate → neither |
| V230 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V232 | OPEN → OPEN | P → P | a → c | candidate → candidate |
| V243 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V244 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V245 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V247 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V257 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V258 | OPEN → OPEN | P → P | a → d | candidate → candidate |
| V370 | OPEN → OPEN | P → P | b → c | neither → neither |
| V373 | OPEN → OPEN | P → P | a → c | neither → neither |
| V374 | OPEN → OPEN | P → P | a → c | neither → neither |
| V396 | OPEN → OPEN | P → P | b → c | neither → neither |
| V400 | OPEN → OPEN | P → P | a → b | neither → neither |
| V403 | OPEN → OPEN | P → P | a → b | neither → neither |

The [owner packet](PV-OWNER-PACKET-20261027.md) lists seven decisions/actions:
client toolchain; release client recipe; N7 custody patch; SHA-NI semantics versus
soft timing; DOITM firmware/Secure Boot; extraction beyond Drop; fixture-harness
versus user-wallet scope. It distinguishes recorded lead recommendations from
worker proposals and undecided alternatives. No new recommendation or adoption
is supplied by this recount.

Validation: 20 statement-only Lean invocations (10 exit 0, 10 exit 1), plus 14
duplicate-guard refusals charged zero; Env-J54200–54233. Standard axioms on
successful checks. Nine failures are missing imported objects; one is a helper
name-parsing error (OptionB), retained without row credit. Duplicate checks were
not resubmitted with cosmetic changes. Existing proof receipts and source hashes
are reused; [receipts](../evidence/privacy-recount-20261026/recount5/receipts.json)
retain commands, revisions, source/dependency hashes, exit, wall, RSS, swap and
complete axioms/errors. No shared source overwrite, local Lean, proof, Kani,
Rust/SBF/runtime gate, full regression, key/fund operation, merge or push.
Stop: every row re-derived and owner packet written. **Target not yet established.**

## Recount 6 2026-10-27 (B)

**Target not yet established.** All 407 rows are re-derived by the
[recount5 method](../evidence/privacy-recount-20261026/recount5/METHOD5.md)
at [immutable pins](../evidence/privacy-recount-20261026/recount6/pins.json).
The prover candidate is exactly **03905a5259**. Running runjoin, reach, batch2
and batch3 heads are snapshots, explicitly recorded as still running; no later
uncommitted or moving-head result is inferred. Historical ledger/recounts1–5
and the owner-decisions section are preserved. [ROWS6](../evidence/privacy-recount-20261026/ROWS6.md)
retains the same columns; [rows6.json](../evidence/privacy-recount-20261026/recount6/rows6.json)
retains historical fields, exact quantifiers, guards, residuals, exclusive buckets,
definition hashes, supporting witnesses and actual consumer import paths.
Source/statement/evidence audit only. Endpoint premises removed/added/weakened:
**0/0/0**; no observer/simE weakening and no new T field.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 | Recount 4 | Recount 5 | Recount 6 |
|---|---:|---:|---:|---:|---:|---:|
| Rows | 400 | 403 | 407 | 407 | 407 | 407 |
| T | 26 | 26 | 26 | 3 | 3 | 3 |
| P | 370 | 372 | 376 | 400 | 400 | 400 |
| C | 4 | 5 | 5 | 4 | 4 | 4 |
| OPEN | 138 | 110 | 103 | 95 | 93 | 86 |
| REDUCED | 152 | 154 | 176 | 176 | 176 | 176 |
| EVIDENCED | 10 | 12 | 14 | 14 | 14 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 | 35 | 37 | 44 |

Seven status changes: the six requested candidate closures and the additional
D285 V178/op26 bounded-P6 closure are independently confirmed. No prior callback
closure is withdrawn by the D188 audit. The six full closing statements, their
carrier/size hypotheses and non-vacuity are read through their source cones,
not inferred from theorem names. [closure audit](../evidence/privacy-recount-20261026/recount6/closure-audit6.json)
records the reasons; the full closing sources are content-addressed by manifest.json.

| Row | Closing law and native evidence boundary | Verdict |
|---|---|---|
| V233/op209 | SplitSelected.native_callback/.consumed; arbitrary Slice U8 at constructed 64-byte storage/trait; SplitObservation.complete includes zero-size error. P6 no-stub native gate lengths 0–129,389 checks, plus 1026 prefixes. Not a native interpretation of every generic ArrayLength. | CONFIRM CLOSED-ON-CANDIDATE |
| V265/op259 | CircleNative.source_reference; CircleSelected.native_source/.consumed, every block/both rows, full Result. Script-checked structural source under(k),8712 finite native comparisons; no raw low-digit defect dependency. | CONFIRM CLOSED-ON-CANDIDATE |
| V184/op33 | MoveWorld/MoveSelected/MoveClosure.complete/.allocation_delta/.nonvacuous; arbitrary non-Copy payload, explicit Buffer.fits/world/memory/frame. Pinned stdlib structural interpretation, Kani lengths 0–4,99 native and33 Drop-ZST cases; no universal raw-pointer/compiler/allocator refinement. | CONFIRM CLOSED-ON-CANDIDATE |
| V261/op254 | B1_254.source; Close254.selected_callback, all N/raw limbs, nonfailure all N, witness N=1; extracted copy plus structural original, restored indexed writes,6144 finite native pairs. | CONFIRM CLOSED-ON-CANDIDATE |
| V247/op230 | B1_230.source; Close230.selected_callback on original callback carrier; symbolic 1024-element Some witness, all lengths/raw limbs, structural original link,320 finite native pairs. | CONFIRM CLOSED-ON-CANDIDATE |
| V264/op258 | B1_258.source; Close258.selected_callback, arbitrary rows/masks/raw limbs, truth/false/bounds errors, nonempty and1025-row failure witnesses; structural original link,896 values/128 errors checked. | CONFIRM CLOSED-ON-CANDIDATE |

V178/op26 is the eighth published library law: CallbackPublication contains the
PV_CBL_CallbackBundle.op26_source declaration. It preserves arbitrary AsRef
Result on the explicit String carrier. Its native gate covers byte lengths 0–2
and every output coordinate; arbitrary native PathBuf/UTF-8 image, allocation/world
and unbounded/deployed association remain. This is the same bounded-P6 accounting
as the earlier seven library laws, not a new deployed source theorem.

The required receipts37698/37699/37600/37604 and38597/38598 are read and parsed,
all exit 0, swap 0, standard axiom subsets. Full commands, source revisions,
dependency fingerprints, timings, RSS and axiom lines remain in
[reused receipts](../evidence/privacy-recount-20261026/recount6/reused-receipts6.json).
37600 is a signature replay paired with37698, not159 additional axiom queries.
165 source-cone occurrences match their final audit freezes; all seven closing
project cones resolve. Candidate Rust hashes match the circle structural gate and
powers-original binding. The native links remain structural/bounded where stated;
no finite differential is promoted to a universal machine theorem.

| Candidate closure route | Recount 5 | Recount 6 |
|---|---:|---:|
| extraction | 27 | 27 |
| extraction bridge | 1 | 1 |
| P6 gate | 8 | 10 |
| structural source | 0 | 4 |
| structural stdlib + bounded gate | 0 | 1 |
| axiom diagnostic | 1 | 1 |

| OPEN dependency | Recount 1 | Recount 2 | Recount 3 | Recount 4 | Recount 5 | Recount 6 |
|---|---:|---:|---:|---:|---:|---:|
| (a) independent proof/evidence | 79 | 51 | 44 | 23 | 10 | 6 |
| (b) native/RunJoin/Records/model instance | 51 | 50 | 51 | 55 | 55 | 56 |
| (c) unresolved owner action | 8 | 9 | 8 | 1 | 6 | 5 |
| (d) exact shared escaping-reference obstruction | 0 | 0 | 0 | 16 | 22 | 19 |

Buckets remain exclusive in d/c/b/a precedence. Of the six requested closures,
V184/V233/V261/V265 leave a, V247/V264 leave d; op26 also leaves d. V370 moves
c→b because D301 approves compiler selection while compiler preservation remains
P. Original exact-guard findings are retained for blocked originals until their
source association is supplied; an accepted copy emission alone is insufficient.

| in headline closure? | Recount 1 | Recount 2 | Recount 3 all / candidate closures | Recount 4 all / candidate closures | Recount 5 all / candidate closures | Recount 6 all / candidate closures |
|---|---|---|---:|---:|---:|---:|
| research | not recorded | not recorded | 160 / 0 | 160 / 0 | 160 / 0 | 160 / 0 |
| candidate | not recorded | not recorded | 133 / 17 | 137 / 29 | 135 / 29 | 129 / 29 |
| neither | not recorded | not recorded | 114 / 10 | 110 / 6 | 112 / 8 | 118 / 15 |

Actual consumer roots from recount5 and their current candidate wire counterparts
are traversed. The historical join snapshot has explicit unresolved transitive
modules; current candidate consumers resolve them, and no guessed source cohort
is substituted. All seven newly credited closing laws are absent from those
consumer cones, although their defining callback signatures were members. V271
now gains defining-source candidate membership after D292. Thus all-row membership
research/candidate/neither is160/129/118; candidate-closure membership is0/29/15.
Membership remains distinct from discharge and is not a deployment claim.

**D188 fidelity.** Owner narrowing is approved by the second amendment and D301.
pv-d188 AUDIT.md retains 33 credit-stands rows,21 native/effect suspensions and
one body-scoped withdrawal qualification at V388. Its41 fresh projection agreements
do not clear 382 unverified declaration occurrences. Raw low_base_p_digits drops
the mutable back-function at 3611 and quotient at 3624: P/P+1/ff disagree; zero agrees.
SDY covers the twelve-leaf raw Funs overlap only: exactly one lost restoration,
and verify_in_place/update_residue_row/add_small_base_p/BatchedWeights.finish
retain writes and agree on the twelve checked fixtures. Ruling(o)/D302 restores
that checked credit, not universal ABI/trace/cohort/native composition. Indexed
Stream B copies bypass the defective raw body; per-function restoration checks
remain required. No closed callback is newly withdrawn. Per-row dispositions
are retained in rows6.json, including V152–V154/V161–V168/V221–V222 suspensions.

**Batch2 failure and repair.** Retain the kernel-checked op253 counterexample:
Variant D/kind 0/j1024 original gives arrayOutOfBounds; old copy gives assertionFailure.
At the pinned running head, authorized repair 5b11c957a0 restores literal frozen
table/indexing. ErrorRepair.op253_counterexample_repaired (52015) proves the
counterexample input and oversized D boundary behavior. Universal valid-input
copy equality and V256–V260 row bridges remain OPEN; no success-only narrowing.

**RunJoin and audits.** Recount 5 records-extraction failure wording is superseded:
runjoin17 identifies extracted records generally, and subsequent jobs prove
fixture compiler returns/transitions, banks/public equality and admitted traces.
runjoin21 is the first passing endpoint axiom audit, attempt 37099, stored under
evidence/pv-runjoin20-20261027/: exit 0,2.260053458s,4,326,617,088bytes RSS,swap 0,
revision 8b9801a9bdf780d3380cb1e1d7bc2a2c66a81ec0; axioms exactly propext,
Classical.choice,Quot.sound.5673 external and669 project objects were verified.
It is focused cached audit evidence, not a final dependency release replay or
row closure. The later38299 import failure remains recorded independently.

D320 corrects the target: Selection.selected is caller-supplied; frozen
RealR1_client takes public/compiled arguments, with fixture-only callers and no
deployment selector. V152 public projection, V153 raw trace and V154 S2/pi/D18
are universal SourceIdentification obligations; V038 ranges over every common
sample. Fixture successes inhabit V047’s fibre and cannot close them. Deployed
public binding, native/caller/RunJoin associations and P∧hypothetical-T non-vacuity
remain. V404/V405 remain invocation/minimality/effect obligations; dictionary
congruence is weaker. Installed op84 forwards its callback Result, correcting
the earlier generic-interface catching concern.

[Corrections D285–D320](../evidence/privacy-recount-20261026/recount6/CORRECTIONS6.md)
preserve failed approaches, original snapshot qualifications and every entry’s
disposition. Material updates are the extra op26 closure; the late original-carrier
bridges qualifying D298; D188’s body/fixture scopes; repaired op253 boundary
with universal equality still open; and D320’s universal target. D318’s a 10→7
summary for its three closures is confirmed. Nonconforming dudect detection was
diagnosed as a harness preparation artifact, not a shipped leak or final pass.

The [owner packet](PV-OWNER-PACKET-20261027.md) marks client toolchain and
D188 narrowing **owner-APPROVED** under D301/second amendment. Open: release
features and constant-time private-input decoding; N7 key custody; SHA-NI
trust/refinement versus soft backend; DOITM implementation; client scope as
devnet fixture harness versus wallet. Each retains question/options/evidence,
only the LOG’s recorded recommendations, and what it unblocks. D291 makes
general extraction strategy information, with SHA wrappers retained in the SHA
decision. Client scope includes the caller-supplied selection consequence.

Validation: source-only audit, **0/20 Lean**,0 Kani, no proofs, no new modules,
no host scope, no ID consumed (39200–39299 reserved). Existing proof/audit
receipts are reused without recompilation. Object authority rulings are binding
but no external object is loaded here. Manifest hashes, every row/status/bucket,
historical fields, import paths and required receipt axioms are checked by
validate6.py. No full regression, runtime/build/ELF gate, Stream A edit, merge,
push or key/account action. Stop: every row re-derived and owner packet updated.
**Target not yet established.**

## Recount 7 2026-10-28 (B)

**Target not yet established.** All407 rows re-derived by the
[recount6 method](../evidence/privacy-recount-20261026/recount6/METHOD6.md),
with [METHOD7](../evidence/privacy-recount-20261026/recount7/METHOD7.md)
and [immutable pins](../evidence/privacy-recount-20261026/recount7/pins.json).
The fixed prover candidate is **6d4350e42c**. runjoin, dlib, b3p6, kstub and
gate6 are live snapshots; reach and l2c are parked snapshots. Their exact heads
are recorded, with no later moving-head result credited. Historical recounts
remain intact. [ROWS7](../evidence/privacy-recount-20261026/ROWS7.md) has the same
columns, exclusive buckets and headline-membership column;
[rows7.json](../evidence/privacy-recount-20261026/recount7/rows7.json) preserves
historical fields, exact definitions, guards, source witnesses and residuals.
Endpoint premises removed/added/weakened: **0/0/0**. T remains exactly
entropy_law, entropy_kernel, observation.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 | Recount 4 | Recount 5 | Recount 6 | Recount 7 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Rows | 400 | 403 | 407 | 407 | 407 | 407 | 407 |
| T | 26 | 26 | 26 | 3 | 3 | 3 | 3 |
| P | 370 | 372 | 376 | 400 | 400 | 400 | 400 |
| C | 4 | 5 | 5 | 4 | 4 | 4 | 4 |
| OPEN | 138 | 110 | 103 | 95 | 93 | 86 | 77 |
| REDUCED | 152 | 154 | 176 | 176 | 176 | 176 | 176 |
| EVIDENCED | 10 | 12 | 14 | 14 | 14 | 14 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 | 87 | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 | 35 | 37 | 44 | 53 |

| OPEN dependency | Recount 1 | Recount 2 | Recount 3 | Recount 4 | Recount 5 | Recount 6 | Recount 7 |
|---|---:|---:|---:|---:|---:|---:|---:|
| (a) independent proof/evidence | 79 | 51 | 44 | 23 | 10 | 6 | 2 |
| (b) native/RunJoin/Records/model instance | 51 | 50 | 51 | 55 | 55 | 56 | 56 |
| (c) unresolved owner action | 8 | 9 | 8 | 1 | 6 | 5 | 5 |
| (d) exact shared escaping-reference obstruction | 0 | 0 | 0 | 16 | 22 | 19 | 14 |

Buckets use d/c/b/a precedence. Four closures leave a (V217,V220,V259,V260);
five leave d (V230,V239,V256,V257,V258). No bucket moves are inferred merely
from a running job. No whole deployed row or endpoint premise is removed.
V152–V154 were REDUCED, so their honest-family discharge is not subtracted
from OPEN. Their original row text is retained with the scope distinction below.

| Row | Closing statement / native evidence boundary | Verdict |
|---|---|---|
| V230/op134 | PV_B3_Close134.source; exact original callback carrier/concrete error type,64 masks,261 callback frames; all136 endpoint pairs and sort/dedup OR transport checked. Nonvacuity length64. | CONFIRM selected candidate closure; structural source |
| V239/op222 | PV_B3_Install222.source; arbitrary raw column/10-point array, full Result/Option, ordered scan/storage/fold, lossless carriers. Empty-column formal witness and nonempty constant-seven native/emission witness kept distinct. | CONFIRM selected candidate closure; structural source |
| V217/op117 | PV_B3_Install117.source; arbitrary raw16/10 coefficients,value,10 points, full Result, no canonicality/source-law premise; symbolic successful zero witness, exact prepared/traversal order. | CONFIRM selected candidate closure; structural source |
| V220/op121 | PV_B3_Install121.source; arbitrary raw28 coefficients/challenge, exact grouped evaluator/full Result, successful symbolic zero witness; no naive Horner substitution. | CONFIRM selected candidate closure; structural source |
| V256/op249; V257/op250 | GammaOriginal/OrdinaryOriginal.copy_equal_original plus F_AuditClosure.closed_rows; every byte slice, complete Result, original carrier and arbitrary-byte sampler success. | CONFIRM two selected candidate closures; structural source |
| V258/op251 | MaterializeRequest.complete_result; ResourceFamilies.heap_source; F_AuditClosure.closed_rows. Every weights/kappa and input-dependent HeapRequest, denied/fail/div retained. Supplied-success witness. | CONFIRM selected candidate closure; structural source |
| V259/op252 | ConstructorEffect.complete_result; ResourceFamilies.box_source; F_AuditClosure.closed_rows. Every variant/raw alpha/points and input-dependent BoxRequest. Shared constructed-weight witness; caller Box repair/layout evidence retained. | CONFIRM selected candidate closure; structural source |
| V260/op253 | RawNative.copy_equal_original/source plus F_AuditClosure.closed_rows. Every kind/index including invalid D; no success-only narrowing. Retained old error counterexample, exact table/guard repair and successful constructor/raw witness. | CONFIRM selected candidate closure; structural source |
| V178,V179,V182,V195,V233 | Closing Lean laws unchanged; complete-body structural bindings, named Lean transports, unchanged domain residuals, fresh same-input native comparisons. | CONFIRM prior closures as structural (K-1 substitute); historical copy-dependent Kani links SUSPENDED |
| V184/op33 | MoveClosure.complete on arbitrary non-Copy payload/world/frame/representable buffer. Independent pinned stdlib move semantics. | STANDS on structural stdlib proof; supporting copy-exposed Kani gate SUSPENDED |

[Closure audit](../evidence/privacy-recount-20261026/recount7/closure-audit7.json)
records full hypotheses/nonvacuity and residuals; source cones and statements are
captured separately. Native differentials are finite validation. Nine new laws
close selected callbacks, not universal native machine/world/allocator, actual
RunJoin installation, D234/V403 reached-input interpretation or L1/L2/L3.
Batch2 resource contexts are arbitrary input-dependent functions; universally
quantifying them does not prove actual OS failure witness independence.
The retained boxed-allocation mismatch led to the authorized caller repair.
Source hash checking finds58/60 exact file matches. The two prover.rs hashes
are historical: constructor-era prepare_opening is byte-identical; the earlier
materialize caller differs only by the authorized retained Box wrapper there.
Other changes are batch3 mask/public-byte routing. Exact deltas and body checks
are in native-pin-exceptions7.json; no file-wide equality is falsely asserted.

K-1: final kscan inventories264 PASS observations,57 copy-exposed,0 unresolved.
The five historical native links are suspended under(r), and independent
structural replacements are accepted under(k'). No historical PASS is used
as a replacement native link. All8,852,102 replacement comparisons agree, as
finite validation only; the old native domains and source-image/lifetime/world
residuals remain. Under(r') exact KMX patch plus a matched failing negative
control is required for Kani re-credit. Pinned kstub has timeouts and partial
positive/control work, not five completed re-verifications. KMX/KMY/KMZ do not
supply those five links: KMZ confirms7 selected Stream A properties, leaves9
OPEN and keeps checkpoint/append suspended (3/12 restored). No Stream A object
was loaded or edited. The tool upgrade is not a copy-fidelity repair.

| Candidate closure evidence class | Recount 6 | Recount 7 |
|---|---:|---:|
| extraction | 27 | 27 |
| extraction bridge | 1 | 1 |
| P6 gate | 10 | 5 |
| structural source | 4 | 13 |
| structural (K-1 substitute) | 0 | 5 |
| structural stdlib + bounded gate | 1 | 0 |
| structural stdlib | 0 | 1 |
| axiom diagnostic | 1 | 1 |

| in headline closure? | Recount 1 | Recount 2 | Recount 3 all / candidate closures | Recount 4 all / candidate closures | Recount 5 all / candidate closures | Recount 6 all / candidate closures | Recount 7 all / candidate closures |
|---|---|---|---:|---:|---:|---:|---:|
| research | not recorded | not recorded | 160 / 0 | 160 / 0 | 160 / 0 | 160 / 0 | 160 / 0 |
| candidate | not recorded | not recorded | 133 / 17 | 137 / 29 | 135 / 29 | 129 / 29 | 120 / 29 |
| neither | not recorded | not recorded | 114 / 10 | 110 / 6 | 112 / 8 | 118 / 15 | 127 / 24 |

Same actual consumer roots as recount6, including current candidate wire
counterparts; no publication root invented as a consumer. All nine new closing
laws are absent from those import cones. Definitions formerly present become
neither when the closing law is the membership criterion: candidate129→120,
neither118→127. Candidate-closure membership remains29, with24 absent.
Membership is not discharge or deployed association.

V152–V154: the original row text refers to the universal raw-family
SourceIdentification handoff. The raw and admission-only conjunctions are
**identification_unsatisfiable**, from the checked cached-column padding
counterexample. V153 contradicts canonical cell(0,13); the raw transport law
V154 remains true, and a public projection may hold even where no record-based
canonical map exists. Do not classify three individual equations as false.
At **PV_RunJoin_HonestIdentification26.source_honest/target**, all three fields
are **discharged at the honest family**, with unchanged generic consumers and
both transfer/withdrawal non-vacuity fixtures. The exact scope sentence is:
**the source handoff covers every compiler-produced input carrying semantic
Admission, full successful return equal to its cached payload with both Result
layers, Checked and canonical frontier words.** This is a separate family
instantiation; the raw theorem is not silently replaced. The endpoint itself
has no SourceIdentification argument and is not shown vacuous by its failure.
No RustRealRefinement conjunct or RunJoin field is removed.

Coverage remains open: successful canonical codec-first preparation implies
HonestInput is not yet proved. Zero change is admitted but native preparation
rejects it for both transfers and withdrawals; positive change is necessary,
not sufficient for the whole honest domain. The raw withdrawal wrapper can
accept noncanonical active frontier words whose payloads fail HonestInput;
the snapshot codec rejects them. Pinned runjoin32 lane progress still leaves
input/append/recipient/sentinel composition. V038 complete common-sample
ROMView/decision agreement with exact marginals and V045 actual native
caller/body/world binding remain. Selection is caller-supplied; fixture
associations do not select a deployment or turn the client into a wallet.

D348: [observer audit](../evidence/privacy-recount-20261026/recount7/D348.md)
finds a **coverage gap**. ROMView exposes model View plus oracle history;
abstract Aux and observer_program do not require a selected total association
for deployed verifier logs/error text on every reached path, including
rejections. Model decision preservation does not prove those published bytes
are included. The owner packet carries the representation/association decision
and expected public-byte determinism argument; no extra counted P row is
fabricated under D348's conditional yes branch. V268–V270 are prover-side
formatting and do not establish verifier log/error determinism.

Integ4/5 evidence applies to03905a5259: matching ELF pins, pinned client,
deterministic fixtures and1000-pair differential; +1.59%/+1.71% is projected
cost. Pinned gate6 has three fresh matching ELF pins, pinned client and coin0
deterministic match on82566acdfb, with full differential/quiet timing pending
in committed evidence. D356's live853/1000 report is not a completed gate.
No final-candidate timing/adoption or privacy release is inferred. Parked
reach/l2c and live dlib/b3p6 keep their rows OPEN; model lemmas, unconfirmed
native gates and no detected leak do not supply universal source/guard laws.
D188's existing body/fixture qualifications remain; K-1 is independently applied.

[Corrections D301–D356](../evidence/privacy-recount-20261026/recount7/CORRECTIONS7.md)
preserve rejected loop repairs, raw-cache counterexamples, nested replay
timeout, K-1 suspensions, partial gates and the distinction between conditional
source handoff, honest-family discharge and complete deployed refinement.
The [owner packet](PV-OWNER-PACKET-20261027.md) retains open decisions on
D338/D342 successful-user domain, client scope/Selection, release features/CT
decoding, N7 custody, SHA-NI, DOITM implementation and the D348 coverage gap.
Only recorded lead recommendations are attributed; none becomes an approval.
Client toolchain and D188 narrowing remain already approved.

Validation: **0/20 Lean,0 Kani**, no proofs/new Lean modules/host scope/ID.
The two interrupted runs used0 attempts; this continuation also used0.
Env-J35200–35299 remains unused. No new statement requiring type-checking was
introduced. Twelve existing proof/audit/replay receipts are independently
parsed with full stdout for wrapped axioms: successful targets, exact source
revisions, wall/RSS/swap and accepted propext/Classical.choice/Quot.sound
subsets are in receipt-audit7.json and reused-receipts7.json. No new proof,
full regression, runtime gate or ELF rebuild was run. Validation checks all
407 statuses, historical fields, exclusive buckets, source hashes, import
paths, K-1 classes and observer gap. No Stream A/soundness edit, merge, push,
wallet/key/account action. Next deliverables: owner scope/observer decisions,
canonical preparation→HonestInput, concrete V038/V045 and final adoption gates.
**Target not yet established.**
