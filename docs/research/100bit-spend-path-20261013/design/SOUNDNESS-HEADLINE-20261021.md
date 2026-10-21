# Consolidated soundness headline

The new `AspisR1.R1FinalSoundnessHeadline.final_soundness` composes the Tag endpoint with `R9PoolConcreteExperiment.deployed_transport`. Both are universal in the same `D`, `d`, and `P`; neither fixes the decision or restricts the prover. The conclusion concerns the constructed logical tx1/Pool instance. Frozen Rust correspondence remains open.

## Verbatim headline statement

The following uses the imports, namespace openings and abbreviations in the new module.

```lean
theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (tape : Tape) (policy : Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) →
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
    /- R13: accepted binary reads give literal matching data; R13-CLOSE,
       batch A on S7, owner Codex. -/
    (h_R13 : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data)
    /- R14 backend: pairing and finalized accumulator; R14-FINISH,
       S4/S5/S8/S9 boundaries, owner Codex. -/
    (h_R14_backend : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    /- R15 writer: authenticated first-match state; TX1-FINISH and read/write
       audits, unconditional frozen-writer preservation still owed, owner Codex. -/
    (h_R15_writer : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    /- R3/R2: actual semantic endpoint with arithmetic/allocation/circle
       boundaries; HCHECKS field table, owner Codex. -/
    (h_R3_semantic : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data)
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire_tag : BoundaryEvidence s → InitialTagDecision.CheckedRejects D d P (Q + 1161))
    (e : RawExtractorCostComposedBin.CostedExtractor) (p : Parameters)
    /- Size-restricted M10 adequacy; length is independent of distinct reads. -/
    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement e p Q)
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100))
```

## Remaining premises and owners

`D`, `d`, `P`, `Q`, `tape`, `policy`, `s`, `source`, `e`, and `p` are universally quantified data, not assertions of correctness. `source` selects decoded public data and row placements; `tape` supplies the saved checkpoint word tape; `policy` supplies Pool guards. In particular, no canonical-prover restriction, concrete-decision equality, or new assumption about `tape` or `policy` is hidden here.

| Premise | Plain-English meaning | Kind | Owner |
|---|---|---|---|
| `hqueries` | The adversary uses at most Q oracle queries. This is the experiment restriction replacing the separate decoder-start restriction. | Model fact / experiment restriction; oracle-decision port must preserve accounting | Adversary caller; lead / oracle-decision prerequisite worker |
| `evidence : BoundaryEvidence s` | Evidence for every named field listed below; no field was deleted by consolidation. | Mixed release boundary, expanded below | Lead and field owners |
| `h_R16_instance` | On accepted non-collision runs, source-selected decoder/public data and rows 31/32 match the compiled instance. | Model fact pending oracle-decision port, then Rust/source join | DECODER-INSTANCE / lead |
| `h_R13` | On accepted non-collision runs, the literal matching-data reader returns the chosen source data. | Model fact pending oracle-decision port, then Rust/source join | R13 / S7 owner |
| `h_R14_backend` | On accepted non-collision runs, pairing checks and the finalized Hchecks accumulator hold for decoded queries. | Model fact pending oracle-decision port, then Rust/source join | R14 / S4, S5, S8, S9 owners |
| `h_R15_writer` | On accepted non-collision runs, every selected query has authenticated first-match data. | Model fact pending oracle-decision port, then Rust/source join | R15 / tx1 writer owner |
| `h_R3_semantic` | On accepted non-collision runs, the parsed rows satisfy the semantic endpoint for the selected data. | Model fact pending oracle-decision port, then Rust/source join | R3/R2 / HCHECKS owner |
| `h_Rwire_tag` | The decision rejects reachable, non-collision, format-checked transcripts with public tag other than 2. | Rust/source join (S2 header check); decision model fact | R-wire / S2 verifier owner |
| `h_M10_ledger` | The supplied value-correct costed extractor satisfies the size-restricted ledger refinement. | M10 cost | M10 pass 6 worker |
| `h_M10_log_length` | Every accepted recorded run, including colliding runs, has log length at most Q+1161. | M10 cost / recorded-experiment accounting | M10 / oracle-decision log prerequisite worker |

The evidence fields are opaque caller-selected propositions, with the intended meanings recorded in `R1FinalSoundness.BoundaryStatements`. Passing the structure does not itself prove a Rust refinement, establish a ROM instantiation, or select a frozen release. The following inventory retains those intended release obligations; it does not claim they have been discharged. Runtime rows use “P2′ family” to distinguish runtime assumptions from source and cost obligations; only `P2_prime` is literally the same-byte assumption.

| Evidence field | Intended meaning | Kind | Owner |
|---|---|---|---|
| `h_P1 : s.P1` | SHA-256 ROM, collision and target-preimage trust assumption. | Rust/source release boundary (cryptographic model trust) | Lead / release premise acceptance |
| `h_P2 : s.P2` | Ownership, permissions, locks, rollback and persistence. | Runtime P2′ family | Lead / runtime |
| `h_P2_prime : s.P2_prime` | Matching checkpoint digests imply the same complete proof and public bytes. | Runtime P2′ | Lead / runtime / R15 read audit |
| `h_P3 : s.P3` | Concatenated SHA, stored-bump PDA and System semantics. | Runtime P2′ family | Lead / runtime |
| `h_P4 : s.P4` | Observed metadata equals runtime owner/signer/writable/executable metadata. | Runtime P2′ family | R16 / runtime |
| `h_P5 : s.P5` | Stored bumps and hints have canonical initializer provenance. | Rust/source join | Initializer / lead |
| `h_P6 : s.P6` | Correct pinned Charon/Aeneas/Lean/mathlib translation and proof toolchain. | Rust/source release boundary (toolchain trust) | Lead / C2 replay |
| `h_P7 : s.P7` | Correct pinned source-to-SBF compilation. | Rust/source release boundary (toolchain trust) | Lead / reproducible-build owner |
| `h_R10 : s.R10` | One complete consistent tx1/tx2 byte log. | Rust/source join | LOG-TX2 / instrumentation owner |
| `h_R22 : s.R22` | Wrapping-source acceptance implies checked-source acceptance in both cones. | Rust/source join | Overflow-freedom owner |
| `h_R4_transport : s.R4_transport` | Scalar/circle carriers and full prefix transport agree with source. | Rust/source join | Sampler rows 25–32 owner |
| `h_R17 : s.R17` | Source fold geometry and stored-domain tables agree. | Rust/source join | Fold geometry / S7 owner |
| `h_R20 : s.R20` | Pool reconstruction and CPI handoff agree for both variants. | Rust/source join | R20 / Pool adapter owner |
| `h_R21 : s.R21` | Source, features, extraction and ELF identify the selected freeze. | Rust/source join | Lead / C1 release owner |
| `h_S1 : s.S1` | Gamma powers, Prepared and tx1-body refinement. | Rust/source join | Concurrent S1 re-pin session |
| `h_S2 : s.S2` | Observer-off verifier and adapter caller correspondence. | Rust/source join | S2 / adapter audit owner |
| `h_S3 : s.S3` | Inactive group/table bits and source classification. | Rust/source join | Concurrent S3 re-pin session |
| `h_S4 : s.S4` | Actual four_dots loop/batch and prefix correspondence. | Rust/source join | Concurrent S4 re-pin session |
| `h_S5 : s.S5` | Canonical pairing/dot kernels and their actual callers. | Rust/source join | Concurrent S5 re-pin session |
| `h_S6 : s.S6` | first/first_decoded and same-byte caller binding. | Rust/source join / runtime P2′ | S6 / read-audit owner |
| `h_S7 : s.S7` | Production query_values/accumulate_batched_with_node correspondence. | Rust/source join | S7 re-pin owner |
| `h_S8 : s.S8` | Accumulator/residue finish and compact check_values correspondence. | Rust/source join | S8 re-pin owner |
| `h_S9 : s.S9` | Factored S2 Libra machine arithmetic and loops. | Rust/source join | Concurrent S9 re-pin session |
| `h_S10 : s.S10` | Complete frozen declaration inventory reconciled with production owners. | Rust/source join | Concurrent S10 inventory session |
| `h_M10_uniform : s.M10_uniform` | Uniform bounded input sizes and overhead constant/degree for the implementation family. | M10 cost | M10 pass 6 / lead |

The logical Pool instance uses same checkpoint bytes by construction. Applying this result to frozen Rust still requires the checkpoint ABI, nested-verifier execution schedule and recorded-log source correspondence (`R9PoolConcreteExperiment.RustPoolEqualsModel`, with `source_caller` and `R9DeployedBinaryExperiment.transport`). P2′ alone does not supply that join. No new Rust-equals-model premise has been inserted in place of transport: this theorem deliberately concludes about the logical model.

## Signature audit against both predecessor lines

Run `python3 docs/research/100bit-spend-path-20261013/evidence/headline-20261021/audit.py`. The committed `audit.json` inventories each binder against all nine predecessors. Whitespace and comments alone are normalized; the five weakenings are checked by exact removal of the added collision antecedent. Every other retained binder is identical after the explicitly displayed model specialization, except the wire law replaced as below. Earlier signatures' deleted binders impose no new requirement.

| Predecessor `final_soundness` | Changes to reach headline | Proofs establishing the change |
|---|---|---|
| `R1FinalSoundnessBinPerQuery` | Remove row31, R18, R19, and transport; weaken five source facts and wire; specialize failure model | All rows below; `BinHonestQueryBudget.recorded_starts` already removes hN in the per-query base |
| `R1FinalSoundnessBinPerQueryRow31` | Same, with row31 already removed | `QueryScanRow31SourcePlacement.instanceFields_row31` |
| `R1FinalSoundnessBinPerQueryR18` | Same, with R18 already removed | R18 endpoint derives checked acceptance and uses binary clean-model composition; no replacement premise |
| `R1FinalSoundnessBinPerQueryR19` | Weaken five source facts and wire; specialize failure model and delete transport | `R19BudgetOriginalReads.original_reads` proves R19 from `hqueries` |
| `R1FinalSoundnessBinPerQueryRWire` | Weaken five source facts and tag law; specialize failure model and delete transport | `RWireCompletion.initialTag_of_completion`, `NoCollRWireCompletion.completion_of_format` |
| `R1FinalSoundnessBinPerQueryNoColl` | Weaken tag law; specialize failure model and delete transport | `InitialTagDecision.checked_of_initialTag`, `checked_strictly_weaker` |
| `R1FinalSoundnessBinPerQueryTag` | Specialize failure model and delete transport only | `R9PoolConcreteExperiment.deployed_transport` |
| `R1FinalSoundnessBinPerQueryR9` | Set tx1/Pool to constructed instance; weaken five source facts and InitialTag; delete transport | Same universal Pool transport, NoColl and InitialTag proofs |
| `R1FinalSoundnessBinPerQueryR9Pool` | Weaken five source facts and InitialTag only | Same NoColl and InitialTag proofs; transport already removed |

For R18 the removed universal public-tag premise is not silently reintroduced: `Checks` and the clean-model argument in the R18 endpoint replace the old tag-dependent cost path. For R19 the all-input budget is a theorem; the hqueries restriction is identical throughout. For hN, `BinHonestQueryBudget.recorded_starts` yields Q+34 decoded first reads from hqueries, and there is no hN binder anywhere in these per-query signatures.

The exact strictly weaker source forms are quoted in the verbatim headline statement above. Each replaces `∀ H, accepts ... → fact` by `∀ H, ¬ binaryCollision ... → accepts ... → fact` (R16 also retains its `BoundaryEvidence s →`). The compiled implications are `NoCollPremiseWeakening.h_R16_instance_of_unconditional`, `.h_R13_of_unconditional`, `.h_R14_backend_of_unconditional`, `.h_R15_writer_of_unconditional`, and `.h_R3_semantic_of_unconditional`. `.restriction_is_strict` supplies the logical strictness witness; this is an antecedent restriction, not a claimed universal strictness counterexample for every fixed decoder/prover.

The exact wire replacement is:

```lean
(h_Rwire_tag : BoundaryEvidence s → InitialTagDecision.CheckedRejects D d P (Q + 1161))
```

`InitialTagDecision.checked_of_initialTag` proves old implies new; `.checked_strictly_weaker` is the compiled strictness witness. Earlier completion implies InitialTag by `RWireCompletion.initialTag_of_completion`. The checked format needed to recover completion is derived inside the Tag endpoint from the five collision-free source facts, not added as a hypothesis.

The exact transport deletion, after specializing Tag, is:

```lean
(h_R9_transport : BoundaryEvidence s → DeployedTransport D d P (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)))
```

`evidence/headline-20261021/signature-deletion-only.diff` shows that deletion and no other statement change. `tag-specialized-before.lean.txt` and `headline-after.lean.txt` retain both statements. The specialization changes the conclusion's subject from an arbitrary rational to this model probability, exactly as in the R9/R9Pool line; it does not prove a transport-free result for an arbitrary deployed failure rational. No change is made to `d`, `P`, the five remaining source facts, or the extractor/cost parameters.

## Exact numeric conclusion

Writing F for `deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)`, the conclusion is

```
F ≤ (Q+34)·15/2^109 + 6·(Q+1161)^2/2^256 + 2^(-126) + 2^(-454).
Q ≤ 14777960484892959601791002642008314224629686680
  → F ≤ (Q+1) / 2^100.
```

These are exact rationals, from `PerAttemptEnvelope.B`, `BinCombinedMerkleCollision.kappa`, and `BinPerQueryNumeric.totalBound`, `Qmax`, `query_normalised`. The theorem also retains expected accepted-attempt cost ≤ `p.attemptBudget`, correctness of every returned witness, and `2^(-126)+2^(-454) ≤ 2^(-120)`. The cost and returned-witness statements are exactly the Tag and R9Pool conclusions. There is no fixed-Q substitution or decimal rounding.

## Validation

The focused validation of the new module uses the retained dependency cache, a private object directory, the shared local Lean mkdir lock, `-j1 -M4400 -DElab.async=false`, and `/usr/bin/time -l`. It performs no dependency rebuild or manifest replay. The import-loading failure and successful focused check are recorded below and in the evidence manifest; no source or environment was rerun unchanged.

Attempt 1 failed at import loading (`unknown module prefix R9TwoTransactionExperiment`), before the theorem or its axioms command was checked. Exit 1, wall 3.8837475003674626 s, peak RSS 712294400 bytes, zero swaps; source revision `771f44d5e`, full source hash and command in the attempt receipt. The manually assembled search path omitted the R9 transport cache. The replacement uses the complete union of the successful Tag and Pool packet search paths, preserving their ordering, with a private object directory first. This is a corrected-environment attempt, not an unchanged-source/environment retry or a dependency rebuild. The environment path is now included in the dependency fingerprint. No axioms result exists for the import-loading failure.

The corrected-environment focused compile succeeded. No proof change was needed. This is local focused composition evidence against the recorded cached objects, not a new coherent release-manifest replay.

| Required field | Successful focused result |
|---|---|
| Exact target | `AspisR1.R1FinalSoundnessHeadline.final_soundness` in `lean/R1FinalSoundnessHeadline.lean`, attempt 2 |
| Exit | 0 |
| Wall time | 4.047768833581358 seconds (compiler invocation; excludes lock wait) |
| Peak RSS | 3632939008 bytes |
| Swaps | 0 |
| Source revision | `2bae89f4270cee7ea36799f5f6b56d94c7e3cd63` |
| Source SHA-256 | `4d33d863370d6cc276406e565f07512d411de298a93f4c2c0a477d08a67b253e` |
| Dependency/environment fingerprint | `4f1fd58baf4188d2a33d1be4aace710d1378a28f1ce927f138017eef8492dfcf` |
| Compiler | Lean 4.32.0, pinned local binary; `-j1 -M4400 -DElab.async=false` |
| Complete axioms result | `'AspisR1.R1FinalSoundnessHeadline.final_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]` |

The full argv, ordered search path, direct object hashes, exit, timing, errors and complete axioms output for **both** invocations are in `evidence/headline-20261021/manifest.json` and the `R1FinalSoundnessHeadline-{1,2}` receipts/logs. Object files remain outside the repository; only their size and SHA-256 are recorded. Only one invocation reached theorem checking; the earlier failed invocation is retained rather than omitted.

Consolidation is complete. Remaining work belongs to the named source/model, runtime and M10 owners above; the oracle-decision port is not performed here. No existing Lean module, candidate re-pin, or concurrent M10 instrumentation file was edited.


## Headline v2: closed concrete M10 extractor (2026-10-21)

`AspisR1.R1FinalSoundnessHeadlineV2.final_soundness` is the new logical soundness headline. It fixes `e := ActualCostedExtractorM10.extractor` and `p := CostedAllocationLedgerM10.params Q`, deletes `h_M10_ledger`, and removes `h_M10_uniform` from the evidence inventory. Every other evidence field and source law is retained. `h_M10_log_length` remains a recorded-experiment obligation, including accepted colliding runs.

### Composition and the embedded uniformity field

The latest C3 addendum describes an R19 ancestry, but the actual checked-in `R1FinalSoundnessBinPerQueryM10Closed.final_soundness` already calls `R1FinalSoundnessHeadline.final_soundness`. It therefore includes the Tag/NoColl and constructed R9Pool reductions with exactly the headline's collision-restricted source laws. There is no incompatible R19 premise to restore.

M10Closed itself still accepts the old evidence structure, including its opaque `h_M10_uniform`. V2 defines fresh local structures with precisely that proposition and field deleted; no existing module is edited. `legacyStatements` internally sets the obsolete field to `True`, and `legacyEvidence` copies all 24 retained proofs and supplies `True.intro`. The existing endpoint is universal in the boundary inventory, so it applies to that inventory. The three evidence-dependent laws are forwarded using the supplied v2 evidence; no old uniformity proof is requested or inferred. `ofLegacy` proves the old evidence requirement implies the new one by field projection. The concrete family's uniform coordinate bound is separately already proved by `ClosedAllocationLedgerM10.uniform`; the opaque old field is not misrepresented as that theorem.

Here is the exact weaker inventory used by all v2 evidence-dependent binders:

```lean
/-- The v1 boundary inventory with only M10_uniform deleted. -/
structure BoundaryStatements where
  P1 : Prop
  P2 : Prop
  P2_prime : Prop
  P3 : Prop
  P4 : Prop
  P5 : Prop
  P6 : Prop
  P7 : Prop
  R10 : Prop
  R22 : Prop
  R4_transport : Prop
  R17 : Prop
  R20 : Prop
  R21 : Prop
  S1 : Prop
  S2 : Prop
  S3 : Prop
  S4 : Prop
  S5 : Prop
  S6 : Prop
  S7 : Prop
  S8 : Prop
  S9 : Prop
  S10 : Prop

/-- The v1 evidence inventory with only h_M10_uniform deleted. -/
structure BoundaryEvidence (s : BoundaryStatements) : Prop where
  h_P1 : s.P1
  h_P2 : s.P2
  h_P2_prime : s.P2_prime
  h_P3 : s.P3
  h_P4 : s.P4
  h_P5 : s.P5
  h_P6 : s.P6
  h_P7 : s.P7
  h_R10 : s.R10
  h_R22 : s.R22
  h_R4_transport : s.R4_transport
  h_R17 : s.R17
  h_R20 : s.R20
  h_R21 : s.R21
  h_S1 : s.S1
  h_S2 : s.S2
  h_S3 : s.S3
  h_S4 : s.S4
  h_S5 : s.S5
  h_S6 : s.S6
  h_S7 : s.S7
  h_S8 : s.S8
  h_S9 : s.S9
  h_S10 : s.S10
```

### Verbatim v2 statement

This uses the namespace openings and `totalBound`, `Qmax` abbreviations in `lean/R1FinalSoundnessHeadlineV2.lean`.

```lean
theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (tape : Tape) (policy : Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) →
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
    /- R13: accepted binary reads give literal matching data; R13-CLOSE,
       batch A on S7, owner Codex. -/
    (h_R13 : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data)
    /- R14 backend: pairing and finalized accumulator; R14-FINISH,
       S4/S5/S8/S9 boundaries, owner Codex. -/
    (h_R14_backend : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    /- R15 writer: authenticated first-match state; TX1-FINISH and read/write
       audits, unconditional frozen-writer preservation still owed, owner Codex. -/
    (h_R15_writer : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    /- R3/R2: actual semantic endpoint with arithmetic/allocation/circle
       boundaries; HCHECKS field table, owner Codex. -/
    (h_R3_semantic : ∀ H,
      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data)
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire_tag : BoundaryEvidence s → InitialTagDecision.CheckedRejects D d P (Q + 1161))
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ ((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)) ∧
    (∀ run coins w, (ActualCostedExtractorM10.extractor.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    ((deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ totalBound Q) ∧
    (Q ≤ Qmax → (deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)) ≤ (Q+1 : ℚ) * (1/(2:ℚ)^100))
```

### Revised premise table

The data are `D`, `d`, `P`, `Q`, `tape`, `policy`, `s`, and `source`. The free extractor and parameter data are removed. There is no new restriction on the prover, decision, tape or Pool policy.

| Premise | Plain-English meaning | Kind | Owner |
|---|---|---|---|
| `hqueries` | The adversary uses at most Q oracle queries. This is the experiment restriction replacing the separate decoder-start restriction. | Model fact / experiment restriction; oracle-decision port must preserve accounting | Adversary caller; lead / oracle-decision prerequisite worker |
| `evidence : BoundaryEvidence s` | Evidence for every named field listed below; no field was deleted by consolidation. | Mixed release boundary, expanded below | Lead and field owners |
| `h_R16_instance` | On accepted non-collision runs, source-selected decoder/public data and rows 31/32 match the compiled instance. | Model fact pending oracle-decision port, then Rust/source join | DECODER-INSTANCE / lead |
| `h_R13` | On accepted non-collision runs, the literal matching-data reader returns the chosen source data. | Model fact pending oracle-decision port, then Rust/source join | R13 / S7 owner |
| `h_R14_backend` | On accepted non-collision runs, pairing checks and the finalized Hchecks accumulator hold for decoded queries. | Model fact pending oracle-decision port, then Rust/source join | R14 / S4, S5, S8, S9 owners |
| `h_R15_writer` | On accepted non-collision runs, every selected query has authenticated first-match data. | Model fact pending oracle-decision port, then Rust/source join | R15 / tx1 writer owner |
| `h_R3_semantic` | On accepted non-collision runs, the parsed rows satisfy the semantic endpoint for the selected data. | Model fact pending oracle-decision port, then Rust/source join | R3/R2 / HCHECKS owner |
| `h_Rwire_tag` | The decision rejects reachable, non-collision, format-checked transcripts with public tag other than 2. | Rust/source join (S2 header check); decision model fact | R-wire / S2 verifier owner |
| `h_M10_log_length` | Every accepted recorded run, including colliding runs, has log length at most Q+1161. | M10 cost / recorded-experiment accounting | M10 / oracle-decision log prerequisite worker |

The retained boundary evidence fields and their owners are:

| Evidence field | Intended meaning | Kind | Owner |
|---|---|---|---|
| `h_P1 : s.P1` | SHA-256 ROM, collision and target-preimage trust assumption. | Rust/source release boundary (cryptographic model trust) | Lead / release premise acceptance |
| `h_P2 : s.P2` | Ownership, permissions, locks, rollback and persistence. | Runtime P2′ family | Lead / runtime |
| `h_P2_prime : s.P2_prime` | Matching checkpoint digests imply the same complete proof and public bytes. | Runtime P2′ | Lead / runtime / R15 read audit |
| `h_P3 : s.P3` | Concatenated SHA, stored-bump PDA and System semantics. | Runtime P2′ family | Lead / runtime |
| `h_P4 : s.P4` | Observed metadata equals runtime owner/signer/writable/executable metadata. | Runtime P2′ family | R16 / runtime |
| `h_P5 : s.P5` | Stored bumps and hints have canonical initializer provenance. | Rust/source join | Initializer / lead |
| `h_P6 : s.P6` | Correct pinned Charon/Aeneas/Lean/mathlib translation and proof toolchain. | Rust/source release boundary (toolchain trust) | Lead / C2 replay |
| `h_P7 : s.P7` | Correct pinned source-to-SBF compilation. | Rust/source release boundary (toolchain trust) | Lead / reproducible-build owner |
| `h_R10 : s.R10` | One complete consistent tx1/tx2 byte log. | Rust/source join | LOG-TX2 / instrumentation owner |
| `h_R22 : s.R22` | Wrapping-source acceptance implies checked-source acceptance in both cones. | Rust/source join | Overflow-freedom owner |
| `h_R4_transport : s.R4_transport` | Scalar/circle carriers and full prefix transport agree with source. | Rust/source join | Sampler rows 25–32 owner |
| `h_R17 : s.R17` | Source fold geometry and stored-domain tables agree. | Rust/source join | Fold geometry / S7 owner |
| `h_R20 : s.R20` | Pool reconstruction and CPI handoff agree for both variants. | Rust/source join | R20 / Pool adapter owner |
| `h_R21 : s.R21` | Source, features, extraction and ELF identify the selected freeze. | Rust/source join | Lead / C1 release owner |
| `h_S1 : s.S1` | Gamma powers, Prepared and tx1-body refinement. | Rust/source join | Concurrent S1 re-pin session |
| `h_S2 : s.S2` | Observer-off verifier and adapter caller correspondence. | Rust/source join | S2 / adapter audit owner |
| `h_S3 : s.S3` | Inactive group/table bits and source classification. | Rust/source join | Concurrent S3 re-pin session |
| `h_S4 : s.S4` | Actual four_dots loop/batch and prefix correspondence. | Rust/source join | Concurrent S4 re-pin session |
| `h_S5 : s.S5` | Canonical pairing/dot kernels and their actual callers. | Rust/source join | Concurrent S5 re-pin session |
| `h_S6 : s.S6` | first/first_decoded and same-byte caller binding. | Rust/source join / runtime P2′ | S6 / read-audit owner |
| `h_S7 : s.S7` | Production query_values/accumulate_batched_with_node correspondence. | Rust/source join | S7 re-pin owner |
| `h_S8 : s.S8` | Accumulator/residue finish and compact check_values correspondence. | Rust/source join | S8 re-pin owner |
| `h_S9 : s.S9` | Factored S2 Libra machine arithmetic and loops. | Rust/source join | Concurrent S9 re-pin session |
| `h_S10 : s.S10` | Complete frozen declaration inventory reconciled with production owners. | Rust/source join | Concurrent S10 inventory session |

Frozen Rust correspondence and the verifier-equals-decision join remain open exactly as in v1. The conclusion is still about the constructed logical tx1/Pool experiment; no Rust correspondence premise is silently discharged by M10 composition.

### Exact cubic cost and unchanged soundness bound

The first conjunct retains the existing parameter-budget conclusion at `CostedAllocationLedgerM10.params Q`; the numerical soundness conjuncts and witness correctness are unchanged after fixing the extractor. In addition, the same module's `accepted_cost_cubic` composes `ClosedAllocationLedgerM10.direct_bound` with finite-tape averaging to give

```
mean_coins (ActualCostedExtractorM10.extractor.eval recordedRun coins).cost
  ≤ 4·CostedAllocationLedgerM10.scale³·(Q+1162)³.
```

This holds for every accepted recorded run using only its retained log-length bound. It has degree three in Q and one fixed concrete scale. It is a separate corollary so the headline's conclusion stays textually identical to v1 after the displayed extractor/parameter specialization. The parameter attempt budget is not claimed to equal this sharper direct bound. The unchanged soundness conclusions remain `F ≤ totalBound Q` and `Q ≤ Qmax → F ≤ (Q+1)/2^100` with the exact constants above.

### Deletion-only signature audit against v1

Run `python3 docs/research/100bit-spend-path-20261013/evidence/headline2-20261021/audit.py`. `data-specialization.diff` explicitly fixes `e` and `p` in v1. `signature-deletion-only.diff` then compares the specialized statement and expanded evidence inventories with v2: its only changes are deletion of `h_M10_ledger`, `h_M10_uniform`, and the unused `M10_uniform` proposition data. Every other binder is textually identical with the local structure names resolved by those inventories; all 24 retained evidence fields have identical names and types. There are no added lines or replacement hypotheses. Both expanded statements are retained as `v1-specialized-before.lean.txt` and `v2-after.lean.txt`; the mechanical result is `audit.json`.

The evidence-domain change in `h_R16_instance`, `h_Rwire_tag` and `h_M10_log_length` uses exactly the weaker inventory quoted above. It does not require a caller to supply any additional proof: the theorem already has `evidence : BoundaryEvidence s`, which those functions receive. Internally, the old endpoint's evidence arguments are ignored in favor of that supplied evidence. No general old-uniformity proof is being fabricated.

### V2 focused validation

One focused local compile passed with the successful M10Closed cache environment, private `/tmp/codex-cx-headline2-20261021-objects`, shared mkdir lock, `-j1 -M4400 -DElab.async=false`, and `/usr/bin/time -l`. No manifest replay, dependency rebuild or second compiler invocation was performed.

| AGENTS.md formal-workflow section 6 field | V2 attempt 1 |
|---|---|
| Exact target | `lean/R1FinalSoundnessHeadlineV2.lean`: `AspisR1.R1FinalSoundnessHeadlineV2.final_soundness` and `accepted_cost_cubic`, plus three adapters |
| Exit status | 0 |
| Wall time | 23.06824562512338 seconds, excluding lock wait |
| Peak RSS | 3660333056 bytes |
| Swaps | 0 |
| Source revision | `122f2db4fa66df20a6d84f8caf76c5b1fe6df4cb` |
| Source SHA-256 | `f3090391663242e2ada796d5ef65e47b4be1c4ebc1ac173decf49593be1ad7c2` |
| Dependency/environment fingerprint | `0baa4b8796746305b9cc6a22d0579c16cb440adac4470a19085896518c180575` |

Full `#print axioms` output:

```
'AspisR1.R1FinalSoundnessHeadlineV2.legacyStatements' does not depend on any axioms
'AspisR1.R1FinalSoundnessHeadlineV2.legacyEvidence' does not depend on any axioms
'AspisR1.R1FinalSoundnessHeadlineV2.ofLegacy' does not depend on any axioms
'AspisR1.R1FinalSoundnessHeadlineV2.final_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.R1FinalSoundnessHeadlineV2.accepted_cost_cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The compiler emitted two style warnings because `legacyEvidence` and `ofLegacy` are proof-valued definitions declared with `def`; both are axiom-free and the focused compile has no errors. The successful source is retained without a cosmetic edit or recompilation. Exact argv, complete ordered search path, direct import hashes, compiler/time logs and object SHA-256/size are in `evidence/headline2-20261021/manifest.json` and `R1FinalSoundnessHeadlineV2-1/`. No object or binary is committed. This is focused composition evidence against retained cached dependencies, not a coherent frozen-release replay.

V2 composition and documentation are complete. The remaining source/model and runtime joins, 24 release evidence fields, and recorded log-length premise remain explicit as listed above.
