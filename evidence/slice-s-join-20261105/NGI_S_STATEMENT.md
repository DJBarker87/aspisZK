# Coherently loaded slice S root statements

All seven roots are CLOSED under the retained hybrid ruling-(y) certificate semantics and trust inventory. These are quotations of EXISTING model-side declarations, not newly stated or re-proved native equivalence or headline security theorems. The unchanged historical source/native certificates, exact caller-domain records, complete certificate-name/owner check and selected-callee denial propagation supply their ledger association.

Each block is the full kernel-loaded `#check @name` output, printed with full names, explicit arguments and universes in NGI_L030. No binder or premise is omitted. Each axiom line is the exact `#print axioms` output; universe suffixes annotate the same three standard axiom constants. NGI_AUDIT.json independently raw-walks every selected root in the same combined import. Definitions and aliases remain the committed predecessor declarations; their ownership and full reference closure passed NGI_SCAN.json.

Retained: P6/D188 option-A semantic transport, std/allocator/SDK/ABI/compiler/source-to-ELF realization, RuntimePersistence, digest/H realization, RuntimeReturnData (nonempty 1..1024; emitted ASR8=792), RuntimeMemcmp and the cryptographic assumptions. L154 is a statement parameter. No trust row is added or removed.

## programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box

Rows TX1:332; CLOSED. Declaration `NFY_NEX_PublicModel.result_state_effects`, owner `NFY_Part058`.

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

## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1

Rows TX1:276, TX2:169; CLOSED. Declaration `NFY_NEM_ValidatorComposed.result_state_effects`, owner `NFY_Part032`.

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

## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1

Rows TX2:165; CLOSED. Declaration `NFY_NEQ_EncoderOracle.result_state_effects`, owner `NFY_Part053`.

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

## programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement

Rows TX2:224; CLOSED. Declaration `NFY_NEU_ReconstructAdopted.result_state_effects`, owner `NFY_Part057`.

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

## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1

Rows TX2:163; CLOSED. Declaration `NFY_NFD_RequestOracle.result_state_effects`, owner `NFY_Part059`.

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

## programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer

Rows TX2:226; CLOSED. Declaration `NFY_NFJ_Scanner.result_state_effects`, owner `NFY_Part060`.

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

## programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result

Rows TX2:219; CLOSED. Declaration `NFY_NEY_EmitComposed.result_state_effects`, owner `NFY_Part058`.

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
