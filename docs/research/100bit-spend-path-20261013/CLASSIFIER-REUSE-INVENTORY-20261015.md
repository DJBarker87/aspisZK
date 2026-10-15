# D1/D2/D3 classifier reuse inventory

Read-only source inventory, row-map correction checked against the current Rust sources at worktree HEAD `ce1fb7255213f5b390048d1ca709fea99176ae62`. The cited Lean sources are pinned by SHA-256 below; the R1 Rust files and hashes are listed in the corrected row-map section. This records callable theorem shapes and remaining interface mismatches; it does not assert that D1, D2, or D3 is discharged.

## Current R1 interface

`lean/UnifiedFiatShamir.lean:23-56`, `AspisR1.UnifiedFiatShamir.soundness_bound`, keeps all three conditions as explicit hypotheses. It accepts arbitrary `extract`, `decision`, and `RoundByRound' rb`; `hD1 : FS2.D1 (UnifiedProtocol.protocol p hD extract) rb`, `hD2` for the same protocol/classifier, and `hD3` for the supplied verifier are passed to `R0C.V3.theorem43`. It already transports D2 through `UnifiedChainDensity.chainDensity`, and supplies the checked chain-read, verifier-read, and injectivity lemmas. The theorem's current result is a mean acceptance-and-extractor-failure bound with `Qtot * maxErr rb.ε 33 + 3*Qtot^2/256^32`.

`lean/UnifiedProtocol.lean:24-32` defines an `r := 33` protocol whose sampler is `UnifiedSampler.samp`, whose decoder is `none`, and whose extractor is exactly the caller's function. `UnifiedSampler.samp` (`lean/UnifiedSampler.lean:53-70`) has the schedule: row 0 is the initial C1 absorb and lambda challenge; rows 1–25 use the ordinary duplex sampler, with row 25 carrying circle point z0; row 26 is the reseeded sampler and carries z1; rows 27–30 are opening challenges; row 31 is the two-fold query sampler; row 32 is rho. Wrong message constructors go through `invalid`, which is explicitly totalized and left for a future classifier/decision to reject (`UnifiedSampler.lean:7-11,41-48`). `UnifiedDecoder.component` (`lean/UnifiedDecoder.lean:25-35`) dispatches to the corresponding typed decoders, but is a decoder for oracle reads and does not define the D1 extractor or round predicate.

## Corrected Rust challenge-row map

The current cost-probe Rust implementation places the challenge values at the same indices as the old 25+2+4+query challenge rows. The crucial detail is that row 0 is the initial C1-containing absorb *and* the lambda draw; it is not a separate C1-only round followed by a shifted semantic schedule. `r1_wire::begin` reads lambda at record 0, chi at 1, theta at 2, zc at 3–12, mu at 13, and eta at 14 (`crates/aspis-r1-cost-probe/src/r1_wire.rs:341-364`). `r1_semantic::verify_observed` reads the ten alphas at 15–24 and circle challenges z0 and z1 at 25 and 26 (`.../r1_semantic.rs:83-100,127-130`). `Prepared::new` reads gamma 27, kappa 28, alpha0 29, alpha1 30, then query and rho; on the two-fold path these are rows 31 and 32 (`.../verifier.rs:85-99`). The one-fold path uses query row 30 and rho row 31.

Thus the current two-fold value map is: rows 0–14 = lambda, chi, theta, zc[0..10], mu, eta; rows 15–24 = alpha[0..10]; row 25 = z0; row 26 = z1; rows 27–30 = gamma, kappa, alpha0, alpha1; row 31 = query; row 32 = rho. This corrects the former “row 0 added a shift” description. The old masked schedule's challenge indices 0–31 align in this ordering; the extra current index is terminal rho at 32. The initial and reseeded hash-chain constructions are still structurally different from the old sampler, so this row-name alignment alone is not a sampler-identity or D2 proof.

The Rust row 0 and 26 payload samplers also have auxiliary state answers in the unified model. Row 26's special reseed is after the z1 challenge and feeds the next opening state; it does not move gamma to row 26. The root's current joint-list classifier route fixes F/Y before gamma and may make the circle rows contribute no soundness event, but that route's classifier theorem remains unproved here. This inventory does not independently declare a zero D2 cost for either circle row.

The current algebraic/extraction chain gives useful *consequent* lemmas, not a classifier:

- `ConcreteBinding.binding` consumes five explicit exclusions (`gammaBad`, `kappaBad`, `firstBad`, `secondBad`, and nonzero gamma), a matching set of size at least 9558, two fold match equations, and the final/boundary equations; it produces one `t ∈ candidates W` satisfying all six functional claims and the constant claim.
- `MatchingSupport.large_matching_implies_claims` packages that result as `MatchingSupport.Claims`, still assuming `Good`, `AcceptedPairing`, and the 9558 matching-support bound.
- `SemanticOpening.large_matching_implies_witness` adds `CandidateDescent.WordTyped` and returns the R1 point/extra/candidate witness.
- `MaskedSemantic.large_matching_extracts` adds the explicit sumcheck checks and universal `OutsideBad` exclusions for every candidate. It returns a candidate with `ProductionHolds`, `CopyLinkBalance`, and `InputNoteExtracted`.
- `SemanticPrefix.large_matching_extracts_of_prefix` derives those `OutsideBad` exclusions from a 25-round old masked `hitFrom` exclusion, but also takes parsed-prefix facts, C2 equality, semantic challenge exclusions, matching premises, and accepted checks.
- `SpendExtraction.large_matching_extracts` strengthens that result to `SpendSemantics.NoteFacts` without new premises about values or output notes.

None of these theorems defines the current `rb.doomed`, derives a current `Good`/`AcceptedPairing`/`checks` bundle from `UnifiedProtocol`'s 33-row parsed prefix, or binds the arbitrary `decision` argument to the semantic predicate. They therefore supply target consequences to a future D3 assembly, but do not themselves prove D1/D2/D3.

## D1 reuse

The generic old definition in `FS2/Statement.lean:171` is `D1 pr rb := ∀ x T, pr.extract x T = none → rb.doomed (emptyPrefix x) T`.

The exact old proof candidate is `R0P.SemSource.d1_of_sourceData` (`R0P/SemSource.lean:38-60`). It proves D1 for `protocol s msg samp decode` with `stateRows s`. `R0C.SemStatement.extract` (`R0C/SemStatement.lean:108-110`) is table-ignoring and returns `some (Classical.choose h)` exactly when `∃ w, s.paymentWitness x w`; `doomed` (`:99-105`) contains the matching negated-witness condition plus no-hit on the empty transcript. `R0P.Mask.combinedD1Z` (`R0P/MaskSource.lean:49-66`) is the corresponding masked duplex D1 instance; it explicitly changes the masked extractor back to the same source-data extractor.

**Exact mismatch:** current `UnifiedProtocol.protocol` receives an arbitrary table-dependent `extract : Public → Table → Option W`, while the old proof is tied to a specific witness-existence extractor (table ignored). Current `soundness_bound` also receives an arbitrary classifier `rb`; the old D1 theorem proves only the `stateRows`/`duplexRowsZ` classifier. Reuse needs a proved extractor-failure implication to the chosen R1 classifier at `emptyPrefix`, or an exact specialization/equality of both interfaces. No such bridge is in the cited current modules.

## D2 reuse

Old D2 is the universal table-switch statement from `FS2/Statement.lean:177-182`: for every round `i`, prefix `P`, message `m`, old table `T'`, new table `T`, if `P.round=i`, `i<r`, and the old predicate says `doomed P T'`, then the current sampler's fresh-answer mass of extensions that are not doomed at `T` is at most `ε i`.

The old assembly candidate is `R0P.Mask.combinedProtocolZ_D2` (`R0P/MaskD2Instance.lean:13-51`). Its explicit premises are four sampler-family equalities: all 25 semantic rows equal `.semantic (semChal s)`, circle rows 25 and 26 equal `circleSample0/1`, and rows `27+j` for four opening rounds equal `DQ.σQ j`. It composes row lemmas from `MaskD2Glue` (semantic row at `:73`, circle rows at `:127` and `:163`) and `MaskOpeningDensity`, using `combinedD2BudgetZ`. These prove conditional row bounds for that old classifier and schedule, not for an arbitrary row predicate.

**Exact mismatch:** the old theorem has 32 challenge rounds: semantic 0–24, circle 25–26, opening 27–30, query 31. The current two-fold Rust challenge values at those indices are lambda/chi/theta/zc/mu/eta and alpha at 0–24, circles z0/z1 at 25–26, opening values at 27–30, and query at 31; current row 32 is terminal rho. There is no semantic-index shift. The unified row-0 initial-C1 sampler and row-26 reseeded sampler have different state-answer/hash-chain structures from the old per-row samplers, and the current classifier is not yet connected to all 33 sampler laws. No theorem in the inspected sources proves a rowwise D2 instance from index alignment alone.

`UnifiedChainDensity.chainDensity` is reusable only *after* `hD2`; it converts that premise into the first-read `ChainDensity` bound. `D2TableBoundary.table_flip_cost` also shows why table dependence cannot be elided: its result is conditional on precisely a D2 premise and old/new classifier facts at the same prefix. The smallest missing interface is a current-row D2 lemma (or a proved simulation to old D2) for each R1 sampler case, with a pointwise containment from “old table says doomed, extension at new table is not doomed” into the corresponding counted per-row event. The existing `ConcreteBinding` cardinalities can supply event sizes once row inputs are fixed, but do not establish that classifier implication or its transcript/table dependence.

## D3 reuse

Old D3 is `∀ H x π T, rb.doomed (pr.transcript H x π pr.r) T → (eval H (V x π)).2 = false` (`FS2/Statement.lean:198-200`). `R0P.Mask.accepted_no_hit_extractedZ` (`R0P/MaskD3Glue.lean:17-111`) is the main extraction candidate: under the old masked `decisionZ=true`, `¬ hitFrom` for `sourceDataWithFallbackZ`, the mask-degree premise, and a nonzero first opening field-challenge condition, it returns an `InputNoteExtracted` trace. `R0P.Mask.d3Z` (`:115-153`) wraps it into D3 for `combinedProtocolZ`, `duplexRowsZ`, and the fixed `combinedDecisionZ`; it also requires `prime = 2^31-1`, `MaskDegree`, and the row-27 sampler equality needed for that nonzero challenge.

The deeper semantic chain is also available: `R0P.SemSource.d3_core` (`R0P/SemD3.lean:88-126`) proves `ProductionHolds ∧ CopyLinkBalance` from `BaseTyped`, `HonestRows`, `VirtualDeg`, `ChecksAccept`, sumcheck checks, and exclusions of `candidateRoundBad` for each of 24 semantic rounds. `accepted_no_hit_extractedZ` parses old `decisionZ=true`, obtains old opening acceptance and no-hit, constructs the masked sumcheck inputs, and reaches that core. Current `SemanticPrefix.large_matching_extracts_of_prefix` (`lean/SemanticPrefix.lean:69-118`) and `MaskedSemantic.large_matching_extracts` (`lean/MaskedSemantic.lean:69-106`) similarly provide candidate-level extraction once the R1 opening conditions are supplied.

**Exact mismatch:** current D3 is for the caller-supplied arbitrary `decision` and the current 33-row `UnifiedVerifier`; old `d3Z` is for fixed `combinedDecisionZ`, a 32-row old protocol, its `valuePrefix`, and its `hitFrom` classifier. There is no current theorem translating final unified acceptance and the selected R1 classifier into old `decisionZ=true` plus old no-hit, nor a completed-trace bridge supplying the R1 premises (`Good`, `AcceptedPairing`, enough matching positions, sumcheck acceptance, semantic prefix checks, and candidate-wide `OutsideBad`). The smallest missing bridge is an R1 terminal-acceptance/no-classifier-hit theorem yielding the existing current R1 extraction result, together with a wrapper proving it implies the exact D3 Boolean conclusion for the chosen `decision`.

## Source pins

All paths below are relative to this worktree. Hashes are SHA-256 of the cited source bytes at the recorded HEAD.

| Source | SHA-256 |
|---|---|
| `docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean` | `e472de7d36479495d55e10436635344bf7d2187f223ae73bd0b1db3c78718b36` |
| `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean` | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemSource.lean` | `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskSource.lean` | `299712d96b2025176c6b959be149b1b546beda21e3c60d2fa8514c367a3e304d` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD2Instance.lean` | `0ad9479ac29e8795f02f420c7b921d4bda14edd9ae4ed29db114ff5139d07b50` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3.lean` | `68cd2542aff4f20ead2f5855663cf3e743817725f2714cc3400a21b0f651c74b` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedFiatShamir.lean` | `92bb8f1a2cee6e6a9d9f76d00ca73cdc65159867f30d09f6d478ee92a57f4a6c` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedProtocol.lean` | `0087deb2a71b080806da8601bf469d623e06a4e83692cbf943339768f28ecb45` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedDecoder.lean` | `1627cc41fb098a7e9abe75184f0d00964b3374b46dd46e1c0ddd308a426b5090` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedChainDensity.lean` | `0b17f5e0f0fb348f6717cb9891a139ae90326bd88b6bd9e2cbca84ca354000d1` |
| `docs/research/100bit-spend-path-20261013/lean/ConcreteBinding.lean` | `d7f87db3d7c6d49f6c5c660812b049982fc9314450eeaef202eff7021942876f` |
| `docs/research/100bit-spend-path-20261013/lean/MatchingSupport.lean` | `a3f4eed1b103cdc9cf8b92a3d37a313759e1324a04af79dc251dad8cde775a5b` |
| `docs/research/100bit-spend-path-20261013/lean/TwoFoldExtraction.lean` | `7fb111f415bebcb3182f6d765608219c9e24c1d355b3f99916bb36bd09a9dc20` |
| `docs/research/100bit-spend-path-20261013/lean/SemanticOpening.lean` | `f9f72d9aaa478b6f751f0760291aced6c04a17ef6c8aebd48009b55406115d93` |
| `docs/research/100bit-spend-path-20261013/lean/MaskedSemantic.lean` | `6cf4e08d2285349beb3bf82276f0e9b37a63c014c5aafdd5ffc9744a917e0ea7` |
| `docs/research/100bit-spend-path-20261013/lean/SemanticPrefix.lean` | `a0e75d2bddea2f3d72b7102b29b099e3f552dd50114b255843685c75e8f23245` |
| `docs/research/100bit-spend-path-20261013/lean/SpendExtraction.lean` | `b1ab643fddcc1ddd4be5e5efa9c7d7291c0067feb9214b2d4bc76a8d8b66a523` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/semantic_wire.rs` | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` |
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
