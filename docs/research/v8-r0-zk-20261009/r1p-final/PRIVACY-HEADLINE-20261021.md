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

## Accounting specialization (cx-priv-acct, 2026-10-21)

This extension uses only new PRIVACY modules. `PrivacyR1AcctBasis` selects the
nested quadratic-coordinate basis `i = (((0,1),0),0)`, `u = ((0,1),0)` over
`ProverCommitWordCarrier.sourceBase` in `WideExact`. `base_coordinates` identifies
the existing M31 algebra map with the nested constant embedding, using uniqueness
of ring homomorphisms from `ZMod P`. Projection to the four coordinates proves
independence. `i_sq`, `u_sq`, and `packing_laws` prove `i² = -1`, `u² = 2+i`, and
`PackField`; these are the QM31 packing coordinates used by the protocol, with no
claim about an optimized Rust implementation.

`PrivacyR1AcctModel` fixes `L₁ = ProverCommitSourceDecoder.L₁` and
`L₂ = ProverCommitSourceDecoder.L₂ = 4096`, and fixes both block budgets to
`Eᵢ = 2Lᵢ`. `cell_count` reuses `source_counts`, whose proof bounds eligible
coordinates by an injection into `Fin 16 × Fin 1024` and free rows by the
subtype injection into `Fin 1024`. It does not enumerate these coordinate sets.
`stream₁/₂`, `blocks₁/₂`, and the **strict** `counter₁/₂` follow symbolically.
The coarse first-stream allowance is `26*1024 + 10*1024 + 4*1024 + 4*1024 = 45056`;
thus `E₁ ≤ 90112`, while `E₂ = 8192`. Both are strictly below `2^64`.

The selected base is `PrivacyR1AcctModel.base template log`, with
`Cm := RIdx → OracleAnswer` and `comLog := log`. The other template fields remain
model data; the protocol wrapper constructs its encodings, decoder and bounded
ROM. `wire_coins` is the identity equivalence on this carrier. This is an explicit
base specialization, not a proof that an arbitrary base's coins have that type.
The fixed-size seed retains `decode`, `fib`, and `opens`; the protocol wrapper
replaces its address, leaf and schedule fields. No decoder or opening-law premise
is proved by that construction.

The accounting endpoint selects the constructed `fsR1P` experiment with eight
attempts. Its real randomness is the finite ROM table times eight attempt secrets;
its ideal randomness is eight ideal coin records times eight field tapes.
Finiteness and nonemptiness use the existing symbolic product/function instances,
not cardinal evaluation. This specialization concerns the mathematical experiment;
it does not identify deployed Rust execution with that experiment.

`cF` remains universally quantified because it occurs only in the untouched
`R_commit_quotient_fibres` premise. No result here claims a value or a law for it.
The quotient-fibre, exhaustion, ordered-log, batch, builder, and both execution
join premises remain. In particular this does not consume or replace the concurrent
prover-commit7 or builder-ref9 work. All requested accounting/model predicates are
true at the stated specialization; there is no false protocol-valued predicate
requiring a counterexample.

### Accounting build evidence

Host env J; launcher `run-joint.sh`; Lean `-M 7000`; cgroup MemoryHigh 5 GiB,
MemoryMax 7 GiB, MemorySwapMax 0. Existing receipts 9600–9616 were checked before
starting; these attempts therefore start at 9700 under the explicit fallback.
Each attempt's source SHA-256, direct-import object fingerprint, source revision,
exit, wall time, peak RSS, swaps, full axioms output and diagnostics are in
[acct-evidence/attempts.jsonl](acct-evidence/attempts.jsonl), with adjacent raw logs.
Failed attempts are retained and were followed only by changed sources. No cap or
recursion/heartbeat limit was raised. No existing shared module or object was
replaced, and no full unchanged regression was rerun.

- Basis: attempt 9704, exit 0, 5.10 s, peak RSS 4,126,340 KiB, 0 swaps.
- Accounting model: attempt 9707, exit 0, 4.28 s, peak RSS 4,263,572 KiB, 0 swaps.

Both successful modules report only `[propext, Classical.choice, Quot.sound]`.
The failed diagnostics' `sorryAx` lines are consequences of elaboration errors;
no admitted declaration occurs in the successful modules.
- Endpoint: attempt 9712, exit 0, 7.51 s, peak RSS 4,154,588 KiB, 0 swaps.
  `eight_pos` has no axioms; the four instances and `privacy_headline_acct`
  use only `[propext, Classical.choice, Quot.sound]`.

The source commits are `e08a73bfa` (basis), `3bcc22c96` (accounting model), and
`7ea3c08ad` (endpoint). [frozen-objects.json](acct-evidence/frozen-objects.json)
records those exact source hashes/commits, successful attempt numbers, retained
object hashes/sizes and direct-import source/object hashes. All three successful
receipt fingerprints still match; direct imported sources match this worktree.
`generate_endpoint.py --check` verifies the endpoint text. No binary is committed.
This is a focused composition on the retained env J closure, not a fresh replay
of the repository-wide release manifest.

### Deletion-only premise signature diff

The comparison first specializes data: `F`, `B`, `base`, `seed`, `L₁`, `L₂`, and
`source` have the explicit meanings above. It selects the proved `hB` and the
identity coin equivalence; the latter is data, so its choice must also be used
in the ordered-log premise. Those substitutions are essential: the claim is not
universal elimination for arbitrary seeds, bases or source experiments. The
verbatim signatures below retain their actual source spelling, including
qualified projections needed by Lean's notation elaborator. No retained logical
premise is strengthened and no logical premise is added. Here is the deletion-only
projection onto named obligations (data specializations are recorded separately):

```diff
- hB
  builder_premises
  R_commit_quotient_fibres
  R_commit_exhaustion
- R_commit_counter₁
- R_commit_counter₂
- R_commit_stream₁
- R_commit_stream₂
- R_wire_coin_carrier
  R_wire_D80_batches
  R_wire_D80_ordered_log
- R_commit_cell_count
- R_commit_blocks₁
- R_commit_blocks₂
- Fintype source.RealRand
- Nonempty source.RealRand
- Fintype source.IdealRand
- Nonempty source.IdealRand
  R_wire_builder_checker_D75_retry
  G_sim_R_wire
```

The observer program and `cF` are retained data, as are `h`, `outputs`, and `x`.
`template`, `log`, `decode`, `fib`, and `opens` parameterize the selected base and
seed records; they are functions/data, not replacement correctness assumptions.

### Verbatim before signature

The following is the exact declaration through its result type from
`R1Z/PrivacyR1Headline.lean` at base `575a3e332`; its namespace variables are
`{CommitHandle Aux : Type}`, `{F : Subfield WideExact}`, `base`, `h`, `B`, `outputs`,
and `x` as declared there.

```lean
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

### Verbatim after scope and signature

The local notation fixes the data before the theorem is stated. The declaration
is copied verbatim from `R1Z/PrivacyR1HeadlineAcct.lean`, through its result type.

```lean
import R1Z.PrivacyR1AcctModel
/-! Accounting-specialized headline. All decoder/execution joins are retained.
The source experiment here is the constructed finite binary-ROM experiment. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineAcct
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)
    (log : (RIdx → OracleAnswer) → (Fin 3 → OracleAnswer) →
      View K CommitHandle Aux R1Bat → Challenges K → List (List UInt8 × OracleAnswer))
local notation "base" => PrivacyR1AcctModel.base template log
variable (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (decode : (Fin PrivacyR1AcctModel.E₁ → OracleAnswer) →
    (Fin PrivacyR1AcctModel.E₂ → OracleAnswer) → Option (Tape K F))
    (fib : Challenges K → Fin 3 → Finset Fib)
    (opens : Challenges K → List (Fin 3 ⊕ RIdx))
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
theorem eight_pos : 0 < (8 : ℕ) := by decide
local notation "source" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
instance real_fintype : Fintype (source).RealRand := inferInstance
instance real_nonempty : Nonempty (source).RealRand := inferInstance
instance ideal_fintype : Fintype (source).IdealRand := inferInstance
instance ideal_nonempty : Nonempty (source).IdealRand := inferInstance
theorem privacy_headline_acct
    (builder_premises : BuilderPremises h B x)
    (cF : ℕ)
    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin ((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).E₁ → OracleAnswer) × (Fin ((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).E₂ → OracleAnswer) =>
        quotientDecode (fun e => ((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).tapeOf e.1 e.2) e = some τ)).card = cF)
    (R_commit_exhaustion : RExh (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂)
    (R_wire_D80_batches : RWireBatches (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))).comLog ((coins).symm rest) roots (view h B outputs x w ch τ) ch =
        (((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).openList ch).map (fun c =>
          (gram (((R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))).pubBytes x) ((R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))).vtag (((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).E₁) (E₂ := ((R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))).E₂) c), ansC roots rest c)))
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : h.Instance),
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

Receipt `source_revision` is the worktree HEAD when the new source was submitted;
`source_sha256` identifies the submitted bytes, and `frozen-objects.json` maps those
bytes to the subsequent source-stage commit. The final generator check and
`git diff --check` pass. The work is committed on
`codex/cx-priv-acct-20261021`; nothing was pushed. The still-open quotient,
exhaustion, builder, batch/log and execution premises listed above are not
accounting failures and were deliberately not discharged by this worker.

## D106 wire/log audit (2026-10-21)

The proposed deletion of `R_wire_D80_batches` and
`R_wire_D80_ordered_log` is obstructed at the model level. The new module
`R1Z/PrivacyR1HeadlineWire.lean` proves that an empty supplied opening list
cannot satisfy the batch law, and that an empty supplied log with a singleton
root opening violates the ordered-log equation for every supplied full tape
and challenge. Env J attempt 9721 compiled all four new theorems (exit 0,
4.17 s, peak 4,127,808 KiB, zero swaps, standard axioms only).

`PhaseProtocolInstanceBin` constructs messages, leaf encoding, addresses and
phase order, while retaining the independent `log`, `fib` and `opens` supplied
by `PrivacyR1AcctModel`. Neither D80 binder contains an intrinsic Rust-source
identification. The batch binder remains an opening-layout contract; the log
binder remains the exact ordered serialization/read-log join once its data
are bound to pinned Rust behavior. See [the detailed audit](WIRELOG-20261021.md)
and [receipts](wirelog-attempts-9720-9799.jsonl) for the precise remaining joins.

No deletion-only endpoint or altered privacy conclusion is claimed. The
before and after D106 signatures are identical: both existing binders remain
verbatim in `privacy_headline_acct`. No predecessor Lean file was edited.
