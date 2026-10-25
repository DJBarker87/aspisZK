import GExq_WrapperAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_AccountExperiment
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

structure FirstInputs (A : Type) where
  entry : Entry
  data : Slice U8
  state : A

structure SecondInputs (A : Type) where
  entry : Entry
  data : Slice U8
  slot : S2W_ExtractionBoundary.Slot
  state : A

abbrev FirstReply (A : Type) := Result (core.result.Result
  (alloc.vec.Vec U8 × Heap (Nat → Record) × A) AdapterRw.Cuts.PE)
abbrev SecondReply (A : Type) := Result (core.result.Result (Heap (Nat → Record) × A) AdapterRw.Cuts.PE)
abbrev Outcome (A : Type) := FirstInputs A × FirstReply A × Option (SecondInputs A × SecondReply A)

/-- Fixed before H. Both submissions contain original account/SDK entries and
instruction bytes. The adaptive second choice consumes the ACTUAL saved bytes,
post-copy heap and allocator state, after all source reply/error handling. -/
def program {A F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A →
      Program Bytes State (SecondInputs A)) : Program Bytes State (Outcome A) :=
  bind adversary fun input =>
    bind (SdkC_Oracle.program (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
      copy allocator input.entry id input.data input.state)) fun reply =>
    match reply with
    | .ok (.Ok (saved,post,final)) =>
      bind (chooseSecond input saved post final) fun next =>
        bind (SdkC_Oracle.program (GExq_InstalledWrapper.second adapter ops stage finish reserved query geo B std hashv
          allocator next.entry id next.data next.slot next.state)) fun out => .done (input,reply,some (next,out))
    | _ => .done (input,reply,none)

#print program
end AspisR1.GExq_AccountExperiment
end
