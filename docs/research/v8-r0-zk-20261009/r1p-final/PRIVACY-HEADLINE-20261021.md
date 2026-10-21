# Consolidated privacy headline

`R1Z.PrivacyR1Headline.privacy_headline` composes D100's H1 quotient endpoint with the builder contracts supplied by D96/D99 and D101–D103. Its conclusion is the identical D94/D100/D99–D103 statistical privacy statement, including an exact error strictly below `2^-100`.

The headline uses the common, witness-local `BuilderPremises` contract. The module proves adapters from the protocol's `PublicBase` plus `BuilderSoundOn`, from the canonical builder, and from the source `RustRuntimeJoin`. This avoids adding the source runtime join to the abstract quotient endpoint. A caller using the source line still owes that join; the adapter does not construct it.

## Verbatim headline statement

The following uses the exact imports, namespace openings, variables and local instance in `lean/R1Z/PrivacyR1Headline.lean`. `K` is `AspisWideTower.WideExact`; `CommitHandle` and `Aux` are arbitrary types, `F : Subfield K`, and `base`, `h`, `B`, `outputs`, `x` have the module declarations. There is no unused `publicWidth` parameter in the elaborated theorem.

```lean
def BuilderPremises : Prop :=
  ∀ w : h.Instance, h.public w = x.1 →
    PublicBase F x.1 ∧ R0Z.HonestValidity.BuilderSoundOn h B x


theorem privacy_headline
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
    (builder_premises : BuilderPremises h B x)
    (cF : ℕ)
    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        quotientDecode (fun e => ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2) e = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```

## Exact error bound

Put `W = (wire base ((base.pubBytes x).length) h B outputs x).toWire`, `Pr = (prover base ((base.pubBytes x).length) h B outputs x seed).toProver`, and `M = 8 * n1 W Pr`. All divisions below are rational:

```
ε = M·W.qmax/2^255 + (M²/2^255 + εexhP 8 L₁ L₂ M)
    + 8·4096/((2^31−1)^4−1) + 16/2^486 + 128·(M+1)/2^190.
ε ≤ 2^-109 + 2^-137 + 2^-454 + 128·(M+1)/2^190 < 2^-100.
```

These are expansions of `PrivacyR1Final.modelError` and `QueryScanFreshUnion.freshBudget`, not decimal estimates. `BuilderProtocolBounds.error_bound` proves the first three numerical allowances; `GamesR1PBin.n1_le` gives `M ≤ 2^25`, hence `M+1 ≤ 2^65`; `QueryScanFreshNumerics.fresh_total_lt_target` proves the strict comparison. No fibre, public-base, builder or execution hypothesis is used to establish the numerical part, so it also holds when there is no matching witness. The observable privacy conclusion uses the same `simE h.transport B outputs x` as both predecessor lines.

## Remaining premises and owners

`base`, `h`, `B`, `outputs`, `x`, `seed`, `cF`, `L₁`, `L₂`, `source`, and `observer_program` are universally quantified data. `seed` chooses a well-typed phase prover; it is not an identification with the frozen Rust prover. All wire/prover expressions use the same `h`, `B`, `x`, `base` and `seed` throughout.

| Premise | Plain-English meaning | Kind | Owner |
|---|---|---|---|
| `hB` | The selected packing basis satisfies the field-packing laws. | Model fact | Packing/tower owner; lead |
| `builder_premises` | For every matching witness, the public statement is in the base field and the builder has base typing, lanes and helper validity. Supplied by one of the three proved adapters. | Rust/source join when instantiated with Rust; model fact for canonical builder | Builder/refinement owner (builder-ref9 continuation); lead |
| `R_commit_quotient_fibres` | Every visible H1/noise quotient tape has the same number `cF` of successful input pairs; ignored H1 coordinates need not be uniform. | Rust/source join | Prover commitment owner (prover-commit7 continuation) |
| `R_commit_exhaustion` | The two rejection decoders satisfy the bounded exhaustion law at `L₁,L₂`. | Rust/source join | Prover commitment/sampler owner |
| `R_commit_counter₁`, `R_commit_counter₂` | Both byte-oracle counters fit within `2^64`. | Rust/source join / accounting | Prover commitment owner |
| `R_commit_stream₁`, `R_commit_stream₂` | Each rejection stream has enough bytes for its declared number of cells: `16L ≤ 8E`. | Rust/source join / accounting | Prover commitment owner |
| `R_wire_coin_carrier` | Wire commitment randomness is equivalent to the retained binary-oracle coin carrier. | Model fact with Rust/source binding owed | Wire/commitment owner |
| `R_wire_D80_batches` | Declared phase batches/openings match the wire's batches. | Rust/source join | Wire/commitment owner |
| `R_wire_D80_ordered_log` | The wire commitment log is exactly the prover's ordered opening grammar, for every full tape and challenge. | Rust/source join | Wire/serialization owner |
| `R_commit_cell_count` | Commitment cells satisfy the declared release size bound. | Rust/source join / accounting | Prover commitment/layout owner |
| `R_commit_blocks₁`, `R_commit_blocks₂` | Oracle blocks in each phase are at most twice its declared cell count. | Rust/source join / accounting | Prover commitment/layout owner |
| `[Fintype source.RealRand]`, `[Nonempty source.RealRand]` | The source real experiment uses a finite nonempty uniform sample carrier. | Model fact | Source experiment owner |
| `[Fintype source.IdealRand]`, `[Nonempty source.IdealRand]` | The source ideal experiment uses a finite nonempty uniform sample carrier. | Model fact | Source experiment/simulator owner |
| `R_wire_builder_checker_D75_retry` | For each matching witness and observer, a real execution join identifies the source real test with the constructed model outside the named real bad event. Includes actual builder/checker/retry behavior. | Rust/source join; runtime execution | Prover/builder/checker/retry and wire owners |
| `G_sim_R_wire` | For every observer, the source simulator's ideal execution joins the constructed ideal model outside `selectedBad`. | Rust/source join; runtime execution | Simulator/wire owner; lead |

The following are release interpretation boundaries, not extra Lean binders. They remain necessary when applying the logical model to a frozen deployed implementation.

| Boundary | Remaining obligation | Kind | Owner |
|---|---|---|---|
| Source builder adapter | Supply `RustRuntimeJoin h`: raw witness/public records, `WitnessOk`, `PubCorr` including empty-root consistency, `RspendPlus` admission including the sentinel, public equality, raw-trace equality and transport equality. `builder_premises_of_source` consumes these records without any tape law. | Rust/source join | Builder/refinement owner; production migration/re-pin owner |
| Actual runs and bytes | Show that the two execution joins concern the same pinned source, actual bytes, oracle schedule and retry behavior as the deployment. | Runtime / Rust/source join | Runtime, wire and release owners |
| P6 | Correct pinned extraction/translation and Lean/toolchain interpretation. No named P6 assumption is silently proved by importing a source module. | P6 boundary | Lead / extraction and replay owner |
| Cryptographic model | Instantiate the classical binary ROM model for the deployed hash and preserve the source experiment's query/accounting semantics. This is statistical privacy in that model. | Model fact / release model trust | Lead / cryptographic model owner |
| Simulation implementation | Provide the source simulator and its execution join; host timing/efficiency is not proved by this statistical theorem. | Runtime / Rust/source join | Simulator owner (G-sim) |

## Signature audit against both predecessor lines

Run `python3 docs/research/v8-r0-zk-20261009/r1p-final/headline-20261021/audit.py`. The committed `audit.json` checks every headline binder against all six predecessor theorem signatures, and checks that their conclusions are identical after whitespace and redundant `(h)` normalization. The builder and fibre replacements are explicitly classified rather than falsely recorded as textual matches.

| Predecessor | Builder change | Tape-law change | Proofs |
|---|---|---|---|
| D94 `PrivacyR1FinalProtocolHistoryReal.privacy_R1_protocol_history_real` | Replace unconditional public-base and builder facts by their matching-witness restriction. | Full-tape law → quotient law. | `builder_premises_of_protocol`; `ProverCommitTapeCompletion.full_fibres_imply_quotient`; D100 endpoint |
| D100 `PrivacyR1FinalProtocolQuotient.privacy_R1_protocol_quotient` | Same matching-witness restriction. | Identical quotient law. | `builder_premises_of_protocol`; direct endpoint application in `privacy_headline` |
| D99 `PrivacyR1FinalRelease.privacy_R1_release` | Generalize the canonical `h`; its builder contract is proved without a new premise when specialized back. | Full-tape law → quotient law. | `builder_premises_canonical`, using `BuilderProtocolInstance.builder_sound` (D96) and `BuilderCanonical.publicBase_map`; full-fibre implication |
| D101 `PrivacyR1FinalReleaseSource.privacy_R1_release_source` | Project `RustRuntimeJoin h` to the used builder/public-base facts. | Full-tape law → quotient law. | `builder_premises_of_source`, using `BuilderRuntimeJoin.builder_refinement_D46_D51`, `join.public_eq`, `BuilderCanonical.publicBase_map`; full-fibre implication |
| D102 `PrivacyR1FinalReleaseSource2.privacy_R1_release_source2` | Same as D101. Its endpoint delegates unchanged to D101. | Same as D101. | D102's exact application of `privacy_R1_release_source`; same adapters |
| D103 `PrivacyR1FinalReleaseSource3.privacy_R1_release_source3` | Same as D101. Its endpoint delegates unchanged to D102. | Same as D101. | D103's exact application of `privacy_R1_release_source2`; same adapters |

Every other premise in the table above is identical to its counterpart in each predecessor, including both execution joins, their bad events, counter/stream/block bounds, `RCommitCount`, wire coin carrier, batch law, full-tape ordered log, finite/nonempty randomness instances and `hB`. None is replaced by a new correctness assertion. Universally quantified experiment and observer data are unchanged. For D99 this comparison specializes the headline to the same canonical `h`; it does not identify an arbitrary Rust prover with the canonical one.

The builder restriction is the formula `∀ w, h.public w = x.1 → PublicBase F x.1 ∧ BuilderSoundOn h B x`. The protocol adapter proves old implies new. As a logical restriction scheme it is strictly weaker: when the matching-witness predicate is empty it is true regardless of the two conclusions, whereas the old conjunction still requires both. This is not a claim of strictness at every fixed `h,B,x` (some specializations make the facts equivalent). The source adapter forgets the extra raw-record, admission and transport evidence; its proof establishes the required implication, without asserting a universal non-implication for every fixed prover. The canonical adapter proves the premise outright. Thus no predecessor caller gains an obligation. In particular, replacing the quotient endpoint's builder premise directly with `RustRuntimeJoin` would not have justified this audit; the common contract avoids that strengthening.

For the tape law, `full_fibres_imply_quotient decode c` gives exactly

```lean
∀ s : SourceTape K F,
  (Finset.univ.filter (fun i => quotientDecode decode i = some s)).card =
    Fintype.card (Padding K F) * c
```

The headline's `cF` must therefore be instantiated with `card(Padding K F) * old_cF` when adapting any full-tape predecessor. Reusing the old numeric `cF` would be incorrect. This is harmless reparameterization of universally quantified data: `cF` occurs only in the fibre premise, never the conclusion. `ProverCommitQuotientStrict.quotient_law_strict` proves strictness of the law replacement with a deterministic section of the ignored coordinates. It does not claim every fixed Rust decoder separates the laws.

There is no carrier obstruction. `quotientDecode decode = Option.map project ∘ decode` consumes exactly the same `decode e = Pr.tapeOf e.1 e.2` returning `Option (Tape K F)`. `SourceTape K F` retains visible H1 coordinates and eligible noise; `Padding K F` retains only ignored H1 coordinates. `completionEquiv`, `quotientFibreEquiv`, `h1_completion`, `ProverCommitQuotientView.view_completion`, and `ProverCommitQuotientObservable.commitment_completion` provide the proved completion/observability path used by D100. The builder contract is about `h.build`, `B`, and `x`, not a second random tape. The ordered-log premise still quantifies over the original full `Tape K F`. The proof does not pass `SourceTape` to that premise or manufacture an identification between unrelated carriers.

D102/D103 add supporting builder lemmas but leave their endpoint signature unchanged; importing their endpoints does not discharge the source join. The headline composes their landed endpoint reductions through the same source adapter and D100's endpoint, rather than rerunning any builder or quotient argument. New concurrent work in prover-commit7 or builder-ref9 is outside this base snapshot and has not been claimed here.

## Validation

The sole focused target is `R1Z/PrivacyR1Headline.lean`, with four `#print axioms` commands for all newly added theorems. Validation uses env J's existing compiled objects through the mandated `run-joint.sh`, attempt 9500, Lean `-j1 -M7000 -DElab.async=false`, a 7 GiB cgroup with `MemoryHigh=5G`, `MemorySwapMax=0`, and the launcher's reservation/locking protocol. No dependency rebuild, manifest replay, Rust gate or key operation is part of this work.

Two driver setup failures occurred before a launcher or Lean process started: the documented top-level launcher path was absent, and the discovered `tools/run-joint.sh` lacked executable permission. The final command invokes that existing script with `sh`; no shared launcher was edited. These failures consumed no attempt and produced no compiler or axioms result. The first preflight revision argument was also corrected to the exact committed revision before the actual invocation.

The single compiler invocation succeeded on the committed source. Direct imported object hashes were unchanged after compilation, and their host source hashes match this worktree. This is a focused composition result using the retained env J cache, not a fresh release-manifest replay.

| Required field | Result |
|---|---|
| Exact target | `R1Z.PrivacyR1Headline.privacy_headline`, module `R1Z/PrivacyR1Headline.lean`, attempt 9500 |
| Exit status | 0 |
| Wall time | 5.82 seconds (compiler invocation; lock waiting excluded) |
| Peak RSS | 4,130,812 KiB |
| Swaps | 0 |
| Source revision | `e6c4183cedcc41e6e3fc0a3f746eb9e763d84291` |
| Source SHA-256 | `6bdf33525afc01faf95125de34ead2af9d877a188387676d7746666380a348af` |
| Dependency/environment fingerprint | `c6b57fa09e3f6a48e2f7b0e367072b1e18fe768817d052e8495c247d016fe864` |
| Reservation | 24 GiB populated + 7 GiB requested; under the 55 GiB host limit |
| Compiler | Lean 4.32.0, env J, `-j1 -M7000 -DElab.async=false` |

Complete axioms output:

```text
'R1Z.PrivacyR1Headline.builder_premises_of_protocol' depends on axioms: [propext, Classical.choice, Quot.sound]
'R1Z.PrivacyR1Headline.builder_premises_of_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'R1Z.PrivacyR1Headline.builder_premises_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'R1Z.PrivacyR1Headline.privacy_headline' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact command, environment, import source/object hashes, output object SHA-256 and size, raw timing, errors (none), and full axioms lines are retained in [the receipt](headline-20261021/receipt-9500.json), [compiler output](headline-20261021/out-9500.log), [timing](headline-20261021/time-9500.log), and [launcher output](headline-20261021/launcher-9500.log). The launcher snapshot and driver are adjacent. No binary or compiled object is committed.

Branch: `codex/cx-priv-headline-20261021`; base: `735d367ae`. The source and evidence stages are `e6c4183ce` and `ddc4a1441`. Only a new Lean module and new report/evidence files were added; no predecessor or concurrent worker file was changed. Nothing was pushed.
