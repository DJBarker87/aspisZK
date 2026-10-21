import CallerStage2Carrier
import AspisR1S4AccumulatorNewEmittedSourceCutV3
import CallerStage2SourceConstructorV3

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4AccumulatorNewConcreteChildrenV4
open AspisR1CurrentCaller

abbrev Variant := AspisR1CurrentCaller.transport.Variant
abbrev QM := AspisR1CurrentCaller.aspis_core.field.QM31
abbrev Wide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact

/-- Source-shape mirrors make the nominal carrier conversion explicit. -/
inductive SourceVariant where
  | S1 | S2 | D
  deriving DecidableEq

structure SourceCM31 where
  a : U32
  b : U32
structure SourceQM31 where
  c0 : SourceCM31
  c1 : SourceCM31
structure SourceWideExact where
  c0 : SourceQM31
  c1 : SourceQM31

/-- Cases-based map from the source enum to the current caller enum. -/
def variantFromSource (v : SourceVariant) : Variant :=
  match v with
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def variantToSource (v : Variant) : SourceVariant :=
  match v with
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def sourceCMToCurrent (x : SourceCM31) : AspisR1CurrentCaller.aspis_core.field.CM31 :=
  ⟨x.a, x.b⟩
def sourceQMToCurrent (x : SourceQM31) : QM :=
  ⟨sourceCMToCurrent x.c0, sourceCMToCurrent x.c1⟩
def sourceWideToCurrent (x : SourceWideExact) : Wide :=
  ⟨sourceQMToCurrent x.c0, sourceQMToCurrent x.c1⟩

/-- Selected accepted generated implementation of `Variant::final_len`,
transported through the explicit finite Variant map. -/
def sourceVariantEq (x y : SourceVariant) : Result Bool := do
  let x1 := match x with | .S1 => 0#isize | .S2 => 1#isize | .D => 2#isize
  let y1 := match y with | .S1 => 0#isize | .S2 => 1#isize | .D => 2#isize
  ok (x1 = y1)
def sourceFolds (v : SourceVariant) : Result Usize := do
  let b ← sourceVariantEq v .S1
  if b then ok 1#usize else ok 2#usize
def sourceFinalLen (v : Variant) : Result Usize := do
  let i ← sourceFolds (variantToSource v)
  let i1 ← 2#usize * i
  1024#usize >>> i1

/-- Source constants and the exact fieldwise maps into the current carrier. -/
def sourceQMZero : SourceQM31 :=
  ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩
def sourceQMOne : SourceQM31 :=
  ⟨⟨1#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩
def sourceWideZero : SourceWideExact := ⟨sourceQMZero, sourceQMZero⟩
def sourceZeroQResult : Result QM :=
  .ok (sourceQMToCurrent sourceQMZero)
def sourceOneQResult : Result QM :=
  .ok (sourceQMToCurrent sourceQMOne)
def sourceZeroWideResult : Result Wide :=
  .ok (sourceWideToCurrent sourceWideZero)

/-- Install the emitted constructor body, with only the allocator's `filled`
operation left as an explicit child. -/
def withConcreteConstructorChildren {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (filled : Usize → QM → Result (core.result.Result
      (Aeneas.Std.alloc.vec.Vec QM) AspisR1CurrentCaller.aspis_core.r0.Error)) :
    AspisR1CallerV4Tx1OpsCut.Ops H :=
  AspisR1S4CallerStage2SourceConstructorV3.withSourceAccumulatorNewResult
    ops sourceFinalLen sourceZeroQResult filled sourceZeroWideResult sourceOneQResult

theorem tx1_success_same_query_initial_next_zero {H : Type}
    (ops : AspisR1CallerV4Tx1OpsCut.Ops H)
    (call : AspisR1Stage2.QueryCall)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : Aeneas.Std.alloc.vec.Vec U8)
    (filled : Usize → QM → Result (core.result.Result
      (Aeneas.Std.alloc.vec.Vec QM) AspisR1CurrentCaller.aspis_core.r0.Error))
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      { withConcreteConstructorChildren ops filled with
        queryLoop := AspisR1S4CallerStage2CarrierV1.stage2QueryLoopAdapter call }
      inst public1 publicBytes proof k hash obs = .ok (.Ok bytes)) :
    ∃ parsed zero prepared scratch initialAcc geom pending outputAcc outputPending
        outputAccS outputPendingS,
      ops.parseShape proof = .ok (.Ok parsed) ∧
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      ops.zero = .ok zero ∧
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) =
        .ok (.Ok prepared, scratch) ∧
      AspisR1Stage2.verifier.candidate.query_loop call proof
        (AspisR1S4CallerStage2CarrierV1.preparedToStage prepared)
        (AspisR1S4CallerStage2CarrierV1.accumulatorToStage initialAcc)
        (AspisR1S4CallerStage2CarrierV1.arrayWideToStage scratch)
        (obs.map (fun f => fun phase =>
          f (AspisR1S4CallerStage2CarrierV1.phaseToCaller phase)))
        (AspisR1S4CallerStage2CarrierV1.geometryToStage geom)
        (AspisR1S4CallerStage2CarrierV1.batchedWeightsToStage pending) k =
          .ok (.Ok (outputAccS, outputPendingS)) ∧
      (withConcreteConstructorChildren ops filled).accumulatorNew
        AspisR1CurrentCaller.transport.Variant.S2 = .ok (.Ok initialAcc) ∧
      AspisR1S4CallerStage2CarrierV1.accumulatorToCaller outputAccS = outputAcc ∧
      AspisR1S4CallerStage2CarrierV1.batchedWeightsToCaller outputPendingS = outputPending ∧
      initialAcc.next = 0#usize := by
  exact AspisR1S4CallerStage2SourceConstructorV3.tx1_success_same_stage2_query_starts_zero
    ops call inst public1 publicBytes proof k hash obs bytes
    sourceFinalLen sourceZeroQResult filled sourceZeroWideResult sourceOneQResult h

#print axioms tx1_success_same_query_initial_next_zero
end AspisR1S4AccumulatorNewConcreteChildrenV4
