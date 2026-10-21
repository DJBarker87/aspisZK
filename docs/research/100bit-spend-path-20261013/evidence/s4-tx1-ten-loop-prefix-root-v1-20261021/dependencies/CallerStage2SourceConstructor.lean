import CallerStage2StartZero
set_option autoImplicit false
namespace AspisR1S4CallerStage2SourceConstructorV1
open Aeneas Aeneas.Std Result

/-- Install the transparent constructor source cut into the current caller's
    operation record. Every other operation remains exactly the caller's slot. -/
def withSourceAccumulatorNew {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (finalLen : AspisR1CurrentCaller.transport.Variant → Result Usize)
    (filled : Usize → AspisR1CurrentCaller.aspis_core.field.QM31 → Result
      (core.result.Result (Aeneas.Std.alloc.vec.Vec AspisR1CurrentCaller.aspis_core.field.QM31)
        AspisR1CurrentCaller.aspis_core.r0.Error))
    (zeroQ : AspisR1CurrentCaller.aspis_core.field.QM31)
    (zeroWide : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact)
    (oneQ : AspisR1CurrentCaller.aspis_core.field.QM31) : AspisR1CallerV4Tx1OpsCut.Ops H :=
  { ops with accumulatorNew := fun v =>
      (AspisR1S4AccumulatorNewSourceCutV1.accumulatorNewBody
        finalLen filled zeroQ zeroWide oneQ v) }

/-- Under the explicit source-installed constructor adapter, a successful tx1
    call reaches the same Stage2 query loop and its initial accumulator has
    next=0. No independent constructor-success or query-loop premise is used. -/
theorem tx1_source_constructor_success_starts_zero {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (call : AspisR1Stage2.QueryCall)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : Aeneas.Std.alloc.vec.Vec U8)
    (finalLen : AspisR1CurrentCaller.transport.Variant → Result Usize)
    (filled : Usize → AspisR1CurrentCaller.aspis_core.field.QM31 → Result
      (core.result.Result (Aeneas.Std.alloc.vec.Vec AspisR1CurrentCaller.aspis_core.field.QM31)
        AspisR1CurrentCaller.aspis_core.r0.Error))
    (zeroQ : AspisR1CurrentCaller.aspis_core.field.QM31)
    (zeroWide : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact)
    (oneQ : AspisR1CurrentCaller.aspis_core.field.QM31)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      { withSourceAccumulatorNew ops finalLen filled zeroQ zeroWide oneQ with
        queryLoop := AspisR1S4CallerStage2CarrierV1.stage2QueryLoopAdapter call }
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    ∃ parsed zero prepared scratch initialAcc geom pending outputAcc outputPending outputAccS outputPendingS,
      ops.parseShape proof = .ok (.Ok parsed) ∧
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      ops.zero = .ok zero ∧
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) =
        .ok (.Ok prepared, scratch) ∧
      AspisR1Stage2.verifier.candidate.query_loop call proof
        (AspisR1S4CallerStage2CarrierV1.preparedToStage prepared)
        (AspisR1S4CallerStage2CarrierV1.accumulatorToStage initialAcc)
        (AspisR1S4CallerStage2CarrierV1.arrayWideToStage scratch)
        (obs.map (fun f => fun phase => f (AspisR1S4CallerStage2CarrierV1.phaseToCaller phase)))
        (AspisR1S4CallerStage2CarrierV1.geometryToStage geom)
        (AspisR1S4CallerStage2CarrierV1.batchedWeightsToStage pending) k =
          .ok (.Ok (outputAccS,outputPendingS)) ∧
      (withSourceAccumulatorNew ops finalLen filled zeroQ zeroWide oneQ).accumulatorNew
        AspisR1CurrentCaller.transport.Variant.S2 = .ok (.Ok initialAcc) ∧
      AspisR1S4CallerStage2CarrierV1.accumulatorToCaller outputAccS = outputAcc ∧
      AspisR1S4CallerStage2CarrierV1.batchedWeightsToCaller outputPendingS = outputPending ∧
      initialAcc.next = 0#usize := by
  exact AspisR1S4CallerStage2StartZeroV1.tx1_success_same_stage2_query_starts_zero
    (ops := withSourceAccumulatorNew ops finalLen filled zeroQ zeroWide oneQ)
    call inst public1 public_bytes proof k hash obs bytes finalLen filled zeroQ zeroWide oneQ (by rfl) h

#print axioms tx1_source_constructor_success_starts_zero
end AspisR1S4CallerStage2SourceConstructorV1
