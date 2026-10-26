import P6C_Extension
import Op5T_CarrierGap
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_CarrierGap
open Aeneas Aeneas.Std Result
open S2W_Trace S2W_ExpandedTrace S2W_ExpandedChildren S2W_TraceSplice
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Op5I_AcceptedCarrierCounterexample (readEvents)

/-- Discharging the five mathematical P6 gates does not identify an arbitrary
erased child's effect log. This is a relative interface countermodel, not a
native execution or a shipped vulnerability; it explains the retained L166
association obligation rather than replacing it with another hypothesis. -/
theorem independent {F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (port : ChildConeJoin (Bytes × State) (Op5T_SamePair.dictionary adapter ops stage finish B std))
    (first : Op5T_Marks.FirstMarks port) (second : Op5T_Marks.SecondMarks port)
    (event : S2W_Trace.Event) (marked : S2W_OuterOccurrences.mark event = some false)
    (accepted : Op5T_Marks.accepted (Op5T_SamePair.dictionary adapter ops stage finish B std) event)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (a : Bytes) (d : State) (bad : d ≠ H a) :
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    ∃ fake : ChildConeJoin (Bytes × State) (Op5T_SamePair.dictionary adapter ops stage finish B std),
      Op5T_Marks.FirstMarks fake ∧ Op5T_Marks.SecondMarks fake ∧
      (∃ before after, events fake event = before ++ [.site .batch0,.child (a,d)] ++ after) ∧
      ∀ (R : Type) (code : Program Bytes State R),
        readEvents (events fake event) ≠ (eval H code).1 := by
  exact ⟨P6C_Extension.boundary hashv sha256 H p1 syscall,
    Op5T_CarrierGap.countermodel adapter ops stage finish B std port first second
      event marked accepted H a d bad⟩

#print axioms independent
end AspisR1.P6C_CarrierGap
end
