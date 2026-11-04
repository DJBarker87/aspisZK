# Honest statement of the checkpoint

The refreshed verifier ledger contains **281/599 CLOSED, 0 QUALIFIED, 318 OPEN** under the retained hybrid native/model certificate semantics. Slice S has 97/97 rows and 7/7 roots CLOSED; Q has 2/2 roots CLOSED (145/161 rows); D has 43/345 rows CLOSED and neither transaction entry occurrence CLOSED. Four S/Q occurrences overlap and count once globally. Pool has no consumer row in this verifier inventory, and its production association remains OPEN.

The expected D47 does not reproduce. The NGB closure moves TX1:004 (CM31::from_m31), TX1:025 and TX2:018 (QM31::from_cm31) into Q. NFT's 12 and NFU's 14 promotions overlap at TX1:342. Thus D = 21 - 3 + 12 + 14 - 1 = 43; global CLOSED = 167 + 89 + 12 + 14 - 1 = 281. No status is inferred from an expectation.

The single requested all-slices import includes NGI/NGE/NGF/NFY, NFS/NFN/NFM/NFP, NFQ/NFT/NFU, NFV's audited cuts and AspisR1.RPx_Deployed.deployed. It fails duplicate original/canonical SDK GuardBody ownership. A separately named verifier-only aggregate passes. The full test is a failure; isolated passing forests do not turn it into an all-slices closure. Exact owners, module provenance and affected scope are in NGJ_CONFLICTS.json.

Fresh audit results: 4,167 verifier roots raw-walk completely with standard axioms only and no collectAxioms disagreement; all eight fixtures pass in the same optimized binary. The 13,375-module verifier scan has zero dangling references, incompatible owners or import mismatches. The separate historical Pool environment raw-walks 103 roots with standard axioms and its same-binary fixtures pass, but its 9,507-module scan has 650 dangling references and 548 import-baseline failures (524 absent independent baselines, 24 differing lists). That is a failing forest, not an all-slices pass. NGJ_SCAN.json retains every defect and distinguishes the environments.

CLOSED roots below are model-side theorems with their exact retained domains. Their source association is the separately validated hybrid native certificate plus caller domains and P6/D188 option-A semantic transport. They are not a single kernel theorem proving arbitrary Rust execution equivalence. No new theorem, premise removal, metric change or source adoption occurs here.

## Exact S and Q theorem statements

These are fresh full kernel-loaded `#check @name` quotations from the passing verifier aggregate, with explicit arguments, full names and universes. Every named root also appears in the authoritative raw ax2 audit. The exact `#print axioms` lines follow each statement. Universe annotations do not add axiom constants. Source/native association remains the validated hybrid packet with caller-established domains and retained trust; no quantifier, hypothesis or conclusion is changed here. All seven S statements match NGI's prior quotation exactly. Q's query_loop TX1/TX2 and for_range model/native-association roots are quoted separately; query_values source/result is supporting composition, not a third Q root.

### Slice S

`NFY_NEX_PublicModel.result_state_effects` (NGJ_L038).

```lean
@NFY_NEX_PublicModel.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (state : State),
  @Eq.{1}
    (Prod.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} NFY_NEX_PublicModel.Statement NFY_NEX_PublicModel.PE))
      (Prod.{0, 0} State (List.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} NFY_NEX_PublicModel.Statement NFY_NEX_PublicModel.PE))
      (Prod.{0, 0} State (List.{0} Unit)) (NFY_NEX_PublicModel.run bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisS6CurrentCodecInstallation.Statement
          AspisS6CurrentCodecInstallation.PE))
      (Prod.{0, 0} State (List.{0} Unit)) (AspisS6CurrentCodecInstallation.decode bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NEX_PublicModel.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NEM_ValidatorComposed.result_state_effects` (NGJ_L038).

```lean
@NFY_NEM_ValidatorComposed.result_state_effects : ∀ {State : Type} (s : NFY_NBN_StatementResult.Statement)
  (state : State),
  have observed :=
    NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane NFY_NEM_LateOracle.late s;
  @Eq.{1} (Prod.{0, 0} NFY_NED_ValidatorTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)))
    (@Prod.mk.{0, 0} NFY_NED_ValidatorTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call))
      (@Prod.fst.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call) observed)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call) observed)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} Unit
          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call))
      (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call)
          (NFY_NED_ValidatorTrace.run s))))
'NFY_NEM_ValidatorComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NEQ_EncoderOracle.result_state_effects` (NGJ_L038).

```lean
@NFY_NEQ_EncoderOracle.result_state_effects : ∀ {State : Type} (s : NFY_NBN_StatementResult.Statement) (state : State),
  have observed :=
    NFY_NEQ_EncoderOracle.run
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
      s;
  @Eq.{1} (Prod.{0, 0} NFY_NED_EncoderTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call)))
    (@Prod.mk.{0, 0} NFY_NED_EncoderTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call))
      (@Prod.fst.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) observed)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) observed)))
    (@Prod.mk.{0, 0} NFY_NBN_StatementEncoderSummary.BytesResult
      (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call))
      (NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s))
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) (NFY_NED_EncoderTrace.run s))))
'NFY_NEQ_EncoderOracle.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NEU_ReconstructAdopted.result_state_effects` (NGJ_L038).

```lean
@NFY_NEU_ReconstructAdopted.result_state_effects : ∀ {State : Type} (request : NFY_NEU_ReconstructAdopted.Request)
  (a : NFY_NEU_ReconstructAdopted.Auth) (c : NFY_NEU_ReconstructAdopted.Candidate) (state : State),
  @Eq.{1}
    (Prod.{0, 0} (Aeneas.Std.Result.{0} NFY_NDM_CohortStatement.Reply)
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)))
    (@NFY_NEU_ReconstructAdopted.run State request a c state)
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0}
          AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
          AdapterRw.solana_program_error.ProgramError))
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)) (AspisR1.NFY_JHf_ReconstructionSlot.source request a c)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (NFY_NEU_ReconstructCore.trace (AspisR1.JHf_Carrier.toRequest request)
          (AspisR1.JHf_Carrier.toAuthenticatedAsq8Accounts a)
          (AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 c))))
'NFY_NEU_ReconstructAdopted.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NFD_RequestOracle.result_state_effects` (NGJ_L038).

```lean
@NFY_NFD_RequestOracle.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (state : State),
  @Eq.{1}
    (Prod.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)) (NFY_NFD_RequestOracle.runSlice bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)) (AspisR1.NFY_JHd_RequestNative.decode bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NFD_RequestOracle.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NFJ_Scanner.result_state_effects` (NGJ_L038).

```lean
@NFY_NFJ_Scanner.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (state : State)
  (reply : List.{0} Aeneas.Std.U8 → List.{0} Aeneas.Std.U8 → Int),
  NFY_NFJ_Comparison.RuntimeMemcmp reply →
    @Eq.{1}
      (Prod.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)))
      (@Prod.mk.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)) (NFY_NFJ_Scanner.run reply bytes)
        (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
      (@Prod.mk.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)) (AspisR1.NFY_JHf_Scan.source bytes)
        (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NFJ_Scanner.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFY_NEY_EmitComposed.result_state_effects` (NGJ_L038).

```lean
@NFY_NEY_EmitComposed.result_state_effects : ∀ {A E : Type} (state : AspisR1.S2I.ReturnData.State A E)
  (s : NFY_NEU_EmitModel.Statement),
  @Eq.{1}
    (Aeneas.Std.Result.{0}
      (Aeneas.Std.core.result.Result.{0, 0} (AspisR1.S2I.ReturnData.State A E) NFY_NEU_EmitModel.ProgramError))
    (@NFY_NEU_EmitModel.run A E
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
      NFY_NEY_EmitComposed.encode
      (fun st bytes =>
        @Aeneas.Std.Result.ok.{0} (AspisR1.S2I.ReturnData.State A E) (@AspisR1.S2I.ReturnData.set A E st bytes))
      state s)
    (@AspisR1.NFY_JHb_Emit.source A E
      (fun st bytes =>
        @Aeneas.Std.Result.ok.{0} (AspisR1.S2I.ReturnData.State A E) (@AspisR1.S2I.ReturnData.set A E st bytes))
      state s)
'NFY_NEY_EmitComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### Slice Q

`AspisR1.NFS_QueryLoopRoot.tx1` (NGJ_L039).

```lean
AspisR1.NFS_QueryLoopRoot.tx1 : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b : AspisR1Stage2.verifier.BatchedWeights) (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) a b →
      @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFG_QueryLoopDefs.State)
          (AspisR1.NFG_QueryLoopDefs.run (AspisR1.NFS_QueryLoopRoot.child base proof p g geometry qPlace gPlace)
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
              (Prod.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B) AspisR1Stage2.verifier.Error
              (@Prod.mk.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B a b)))
          (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a g
            (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯))
'AspisR1.NFS_QueryLoopRoot.tx1' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`AspisR1.NFS_QueryLoopRoot.tx2` (NGJ_L039).

```lean
AspisR1.NFS_QueryLoopRoot.tx2 : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b : AspisR1Stage2.verifier.BatchedWeights) (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) a b →
      @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
          (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
        @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFG_QueryLoopDefs.State)
          (AspisR1.NFG_QueryLoopDefs.run (AspisR1.NFS_QueryLoopRoot.child base proof p g geometry qPlace gPlace)
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯)
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
              (Prod.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B) AspisR1Stage2.verifier.Error
              (@Prod.mk.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B a b)))
          (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a g
            (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
'AspisR1.NFS_QueryLoopRoot.tx2' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`AspisR1.NFS_QueryValuesPacket.source` (NGJ_L039).

```lean
AspisR1.NFS_QueryValuesPacket.source : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
  (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_AccumDomain.Input p a pending →
      @Eq.{1} (AspisR1.NFP_TraceTypes.M AspisR1.NFP_QueryCuts.Out)
        (AspisR1.NFS_QueryValuesPacket.run base proof p a g geometry pending qPlace gPlace)
        (AspisR1.NFP_QueryTrace.run (AspisR1.NFS_QueryOps.installed base) proof p a g geometry pending)
'AspisR1.NFS_QueryValuesPacket.source' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`AspisR1.NFS_QueryValuesPacket.result` (NGJ_L039).

```lean
AspisR1.NFS_QueryValuesPacket.result : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
  (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_AccumDomain.Input p a pending →
      @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFP_QueryCuts.Out)
        (@AspisR1.NFI_TraceResult.M.result AspisR1.NFP_TraceTypes.Event AspisR1.NFP_QueryCuts.Out
          (AspisR1.NFS_QueryValuesPacket.run base proof p a g geometry pending qPlace gPlace))
        (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values (AspisR1.NFS_QueryOps.installed base) proof p a g
          (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry pending)
'AspisR1.NFS_QueryValuesPacket.result' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFN_NFB_GeometryComposed.result_state_effects` (NGJ_L039).

```lean
@NFN_NFB_GeometryComposed.result_state_effects : ∀ {State Event : Type}
  (queries :
    Aeneas.Std.Array.{0} Aeneas.Std.U32
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
  (start finish : Aeneas.Std.Usize) (state : State),
  @Eq.{1}
    (Aeneas.Std.Result.{0}
      (Prod.{0, 0} (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G VTop_Stages.verifier.Error)
        (Prod.{0, 0} State (List.{0} Event))))
    (@NEB_PureFrame.run
      (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G VTop_Stages.verifier.Error) State Event
      state
      (@AspisR1.Port3_QueryInstall.result NFN_NEW_GeometryRawInterface.O.G
        (@AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
          (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.N.G NFN_NEW_GeometryRawInterface.N.E)
          (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G AspisR1Stage2.verifier.Error)
          NFN_NEW_GeometryRawInterface.answer
          (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))))
    (@NEB_PureFrame.run
      (Aeneas.Std.core.result.Result.{0, 0} AspisR1Stage2.verifier.QueryGeometry VTop_Stages.verifier.Error) State Event
      state
      (@AspisR1.Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.CE NFN_NEW_GeometryDictionary.adopted queries
        start finish))
'NFN_NFB_GeometryComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

`NFN_NFB_GeometryComposed.accepted_physical` (NGJ_L039).

```lean
NFN_NFB_GeometryComposed.accepted_physical : ∀
  (queries :
    Aeneas.Std.Array.{0} Aeneas.Std.U32
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
  (start finish : Aeneas.Std.Usize),
  NFN_NFB_RangeTrace.Deployed start finish →
    ∀ (heap : NFN_NFB_PhysicalFrame.Heap) (out : AspisR1Stage2.verifier.QueryGeometry),
      @Eq.{1}
          (Aeneas.Std.Result.{0}
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E))
          (@AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.N.G NFN_NEW_GeometryRawInterface.N.E)
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E)
            NFN_NEW_GeometryRawInterface.answer
            (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))
          (@Aeneas.Std.Result.ok.{0}
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E)
            (@Aeneas.Std.core.result.Result.Ok.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E
              out)) →
        ∃ rows lines flat prefixes product suffix resized inverse groups,
          And
            (@Eq.{1} Nat (@List.length.{0} NFN_NFB_GatherTrace.Row rows)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize finish)
                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize start)))
            (And
              (@Eq.{1} (List.{0} Aeneas.Std.U32)
                (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                  (fun l => @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max) flat)
                (@List.flatMap.{0, 0} NFN_NFB_GatherTrace.Row AspisR1.Port4C_GeometryGather.M
                  (fun r => AspisR1.Port4C_GeometryGather.Row.words r) rows))
              (And
                (@Eq.{1} (List.{0} Aeneas.Std.U32)
                  (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                    (fun l => @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max) lines)
                  (@List.map.{0, 0} NFN_NFB_GatherTrace.Row AspisR1.Port4C_GeometryGather.M (fun r => r.lineZ) rows))
                (And (@Eq.{1} Aeneas.Std.Usize out.start start)
                  (And (@Eq.{1} (Aeneas.Std.alloc.vec.Vec.{0} AspisR1Stage2.aspis_core.field.M31) out.line_z lines)
                    (And
                      (@Eq.{1}
                        (Aeneas.Std.alloc.vec.Vec.{0}
                          (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                        out.inverses groups)
                      (And
                        (@Eq.{1}
                          (Aeneas.Std.Result.{0}
                            (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} AspisR1Stage2.aspis_core.field.M31)
                              AspisR1Stage2.aspis_core.field.M31))
                          (@AspisR1.Port3_NativeGeometryBody.Ops.op13 NFN_NEW_GeometryDictionary.CE
                            NFN_NEW_GeometryDictionary.adopted (@Aeneas.Std.alloc.vec.Vec.deref Aeneas.Std.U32 flat))
                          (@Aeneas.Std.Result.ok.{0} (Prod.{0, 0} NFN_NFB_GatherTrace.Vec Aeneas.Std.U32)
                            (@Prod.mk.{0, 0} NFN_NFB_GatherTrace.Vec Aeneas.Std.U32 prefixes product)))
                        (And
                          (@Eq.{1} Nat
                            (@List.length.{0} Aeneas.Std.U32
                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                prefixes))
                            (@List.length.{0} Aeneas.Std.U32
                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                flat)))
                          (And
                            (@Eq.{1} (Aeneas.Std.Result.{0} AspisR1Stage2.aspis_core.field.M31)
                              (@AspisR1.Port3_NativeGeometryBody.Ops.op11 NFN_NEW_GeometryDictionary.CE
                                NFN_NEW_GeometryDictionary.adopted product)
                              (@Aeneas.Std.Result.ok.{0} Aeneas.Std.U32 suffix))
                            (And
                              (@Eq.{1} (List.{0} Aeneas.Std.U32)
                                (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                  (fun l =>
                                    @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                  resized)
                                (@List.replicate.{0} (Aeneas.Std.UScalar Aeneas.Std.UScalarTy.U32)
                                  (@List.length.{0} Aeneas.Std.U32
                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                      (fun l =>
                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                          Aeneas.Std.Usize.max)
                                      flat))
                                  (Aeneas.Std.U32.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                    ⋯)))
                              (And
                                (@Eq.{1}
                                  (Aeneas.Std.Result.{0}
                                    (Aeneas.Std.alloc.vec.Vec.{0} NEW_GeometryActual.aspis_core.field.M31))
                                  (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
                                    (AspisR1.Port4C_Reverse.reverse
                                      (@Aeneas.Std.alloc.vec.Vec.len.{0} Aeneas.Std.U32 flat))
                                    flat prefixes suffix resized)
                                  (@Aeneas.Std.Result.ok.{0} NFN_NFB_GatherTrace.Vec inverse))
                                (And
                                  (@Eq.{1} Nat
                                    (@List.length.{0} Aeneas.Std.U32
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        inverse))
                                    (@List.length.{0} Aeneas.Std.U32
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        flat)))
                                  (And
                                    (NFN_NEW_GeometryReverse.Trace
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        flat)
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        prefixes)
                                      (@List.length.{0} Aeneas.Std.U32
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat))
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        resized)
                                      suffix
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        inverse)
                                      (NFN_NEW_GeometryReverse.suffixAfter
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat)
                                        (@List.length.{0} Aeneas.Std.U32
                                          (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                            (fun l =>
                                              @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                Aeneas.Std.Usize.max)
                                            flat))
                                        suffix)
                                      (NFN_NEW_GeometryReverse.callLog
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat)
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          prefixes)
                                        (@List.length.{0} Aeneas.Std.U32
                                          (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                            (fun l =>
                                              @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                Aeneas.Std.Usize.max)
                                            flat))
                                        suffix))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                            (Aeneas.Std.Usize.ofNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                        (@Subtype.val.{1}
                                          (List.{0}
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat
                                              (@List.length.{0}
                                                (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                                l)
                                              Aeneas.Std.Usize.max)
                                          out.inverses)
                                        (@List.map.{0, 0} Nat AspisR1.Port4C_CollectLoop.Group
                                          (AspisR1.Port4C_CollectLoop.record inverse)
                                          (List.range
                                            (@List.length.{0} Aeneas.Std.U32
                                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                    Aeneas.Std.Usize.max)
                                                lines)))))
                                      (And
                                        (@Eq.{1}
                                          (NFN_NFB_CollectorTrace.Guard
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                          (@NFN_NFB_CollectorTrace.finish
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                            (@NFN_NFB_CollectorTrace.fill
                                              (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                (Aeneas.Std.Usize.ofNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                              (@Subtype.val.{1}
                                                (List.{0}
                                                  (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0}
                                                      (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                        (Aeneas.Std.Usize.ofNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                          ⋯))
                                                      l)
                                                    Aeneas.Std.Usize.max)
                                                out.inverses)
                                              (@NFN_NFB_CollectorTrace.Guard.mk
                                                (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                                (@List.nil.{0}
                                                  (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                          (@NFN_NFB_CollectorTrace.Guard.mk
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                            (@Subtype.val.{1}
                                              (List.{0}
                                                (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                              (fun l =>
                                                @LE.le.{0} Nat instLENat
                                                  (@List.length.{0}
                                                    (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                      (Aeneas.Std.Usize.ofNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                        ⋯))
                                                    l)
                                                  Aeneas.Std.Usize.max)
                                              out.inverses)
                                            (@List.length.{0}
                                              (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                (Aeneas.Std.Usize.ofNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                              (@Subtype.val.{1}
                                                (List.{0}
                                                  (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0}
                                                      (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                        (Aeneas.Std.Usize.ofNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                          ⋯))
                                                      l)
                                                    Aeneas.Std.Usize.max)
                                                out.inverses))))
                                        (And
                                          (@Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                            (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows)
                                              (NFN_NFB_ReturnedBuffers.initial heap)
                                              NFN_NFB_PrivateFrame.Place.lines.id)
                                            (@Option.some.{0} (List.{0} AspisR1Stage2.aspis_core.field.M31)
                                              (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.M31)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0} AspisR1Stage2.aspis_core.field.M31 l)
                                                    Aeneas.Std.Usize.max)
                                                out.line_z)))
                                          (And
                                            (∀ (count : Nat),
                                              @Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                                (NFN_NFB_PhysicalFrame.run
                                                  (@List.take.{0} NFN_NFB_PhysicalFrame.Action count
                                                    (NFN_NFB_GatherFrame.actions rows))
                                                  (NFN_NFB_ReturnedBuffers.initial heap)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (heap (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                            (∀ (count : Nat),
                                              @Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                                (NFN_NFB_PhysicalFrame.run
                                                  (@List.take.{0} NFN_NFB_PhysicalFrame.Action count
                                                    (NFN_NFB_TerminalFrame.actions
                                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                            Aeneas.Std.Usize.max)
                                                        flat)
                                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                            Aeneas.Std.Usize.max)
                                                        prefixes)
                                                      suffix
                                                      (@List.length.{0} Aeneas.Std.U32
                                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                          (fun l =>
                                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                              Aeneas.Std.Usize.max)
                                                          flat))
                                                      (@Subtype.val.{1}
                                                        (List.{0}
                                                          (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                            (Aeneas.Std.Usize.ofNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                (instOfNatNat (nat_lit 5)))
                                                              ⋯)))
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat
                                                            (@List.length.{0}
                                                              (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                                (Aeneas.Std.Usize.ofNat
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                    (instOfNatNat (nat_lit 5)))
                                                                  ⋯))
                                                              l)
                                                            Aeneas.Std.Usize.max)
                                                        groups)))
                                                  (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows)
                                                    (NFN_NFB_ReturnedBuffers.initial heap))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (heap
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                    (instOfNatNat (nat_lit 0)))))))))))))))))))))
'NFN_NFB_GeometryComposed.accepted_physical' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## Missing complete transaction and Pool joins

NGJ_SHORTEST_PATHS.md gives the ordered necessary OPEN entry chains. TX1:330 -> 333 -> 344 -> 345 -> 328 -> 094; TX2:213 -> 221 -> 240 -> 241 -> 064 -> 065 -> 115. Each still needs same-execution physical caller/domain/Result/state/effect association, plus all reached child domains. A dependency path is not an execution CFG or proof of acceptance coverage. The complete list of reachable OPEN occurrences is preserved in NGJ_SHORTEST_PATHS.json.

NFV_REMAINING.md B/D applies verbatim in substance: B must establish the full admitted production prefix, exact request/accounts/borrow/layout/payer/system/marker/custody state, actual selected program/registry/meta keys and SAME request/payment-child domains, in Pool-admission -> CPI -> verifier-admission order. C's controlled cuts need that context; D must instantiate those native facts and NFR_ModelJoin on the SAME production execution. No NFV_PoolReturnData.association is available. Existing value laws do not supply these native facts. The inherited Pool legacy ownership/reference defects additionally prevent a coherent joint import.

## Retained trust and release gates

NGJ_TRUST_USED.json lists direct row tags and retained root context separately. P6/D188 option A is reclassification, never removal; std/allocator/SDK/ABI/compiler/Aeneas/source-to-ELF remain. RuntimePersistence, digest/H realization, RuntimeReturnData (nonempty 1..1024, ASR8=792) and RuntimeMemcmp's exact 688-byte zero/equality contract remain ACCEPTED. Cryptographic premises remain. Pool A's (af) disposition retains std/allocator realization. No (ah) helper credit is inferred from unimported work. L154 is a statement parameter; digest/error are op43/op44.

L159/L181 native realization obligations remain; reclassified release-route trust is not a native discharge. L187 requires a coherent cold replay, full reachability and exact library/object pins. L188 requires the final trust/axiom/source/artifact audit, with native extraction/association obligation 2 still OPEN. This focused cached-cohort validation does not replace those gates. Frozen crates/programs remain byte-identical to 4bb3b3f5; no ELF rebuild was triggered. ELF hashes are inherited, not newly reproduced here.

The 100-bit PER-ATTEMPT release target, privacy and two-transaction design are unchanged.

**target not yet established**
