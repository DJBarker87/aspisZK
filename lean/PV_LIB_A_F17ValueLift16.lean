import PV_LIB_A_F17Value16
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F17ValueLift16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

def base (p : Parameters) : Carrier OWNER Data :=
  PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier
    (PV_THR2_OperatorSemantics_14121.carrier
      (PV_THR2_OperatorSemantics_14119.carrier
        (PV_THR2_BoxDynBinaryLayout.symbols p.loadBias p.siteIndex)
        (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
          (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier
            (PV_THR2_OperatorCarrier.carrier p.primitives)))) p.needsDrop))))

theorem carrier (p : Parameters) : (runtime p).carrier =
    PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (base p)) p.needsDrop := rfl

theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (v : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,3,[]⟩ = some (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v])) :
    ∀ k, k<8 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 7},parents,s⟩,w,es⟩) := by
  have shape : PV_THR2_F17.live.body.drop 7 =
      [PV_THR2_F17.node7,PV_THR2_F17.node8,PV_THR2_F17.node23,
       PV_THR2_F17.node24,PV_THR2_F17.node25,PV_THR2_F17.node26,
       PV_THR2_F17.node27,PV_THR2_F17.node37] ++ PV_THR2_F17.live.body.drop 15 := rfl
  intro k hk
  rw [shape]
  generalize hrest : PV_THR2_F17.live.body.drop 15 = rest
  have tag : (runtime p).control.variant (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) = some 0 := rfl
  have field : (runtime p).carrier.field (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) 0 = some v := rfl
  have moved : (runtime p).carrier.replaceField (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) 0 none =
      some PV_THR2_RunWithValue.emptied := rfl
  have emptyTag : (runtime p).control.variant PV_THR2_RunWithValue.emptied = some 0 := rfl
  simp only [PV_THR2_RunWithValue.emptied] at moved emptyTag
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F17.node7,PV_THR2_F17.node8,PV_THR2_F17.node23,PV_THR2_F17.node24,
    PV_THR2_F17.node25,PV_THR2_F17.node26,PV_THR2_F17.node27,PV_THR2_F17.node37,
    PV_THR2_F17.block9,PV_THR2_F17.block28,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,
    readAddress,readFields,replaceFields,write,cell,tag,field,moved,emptyTag,selectVariant]

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (v : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,3,[]⟩ = some (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v])) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 8
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 7},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F17.live.body.drop 15},parents,
        PV_THR2_RunWithValue.prepared s a v⟩,w,es⟩,[]⟩ := by
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ (clear p H s a parents v w es cell)]
  have existing := PV_THR2_RunWithValue.prepare (base p) p.control
    PV_LIB_SPEC_Full.programs H s a parents v p.needsDrop w es cell
  exact congrArg (fun q => (⟨q,[]⟩ : PV_LIB_StoreActionTable.State)) existing

#print axioms carrier
#print axioms clear
#print axioms source
end PV_LIB_A_F17ValueLift16
