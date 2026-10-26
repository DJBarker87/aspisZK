import SCH_WrapperFirst
import SCH_WrapperSecond
import SCG_AcceptedPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AccountLog
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment SCE_Execution GExq_AccountExperiment

abbrev body1 {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (id : S2W_ExtractionBoundary.Program)
    (i : FirstInputs A) := GExq_Caller.first c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv id i.entry.first i.data
abbrev body2 {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (id : S2W_ExtractionBoundary.Program)
    (i : SecondInputs A) := GExq_Caller.second c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv id (i.entry.second secondSizes) i.data i.slot

theorem chronological {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State)
    (success : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ saved post final,
      (eval H (account c hashv copy allocator id a)).1 =
        (eval H a.first).1 ++
        (eval H (SdkC_Oracle.program (body1 c hashv id (eval H a.first).2))).1 ++
        (eval H (a.second (eval H a.first).2 saved post final)).1 ++
        (eval H (SdkC_Oracle.program (body2 c hashv id
          (eval H (a.second (eval H a.first).2 saved post final)).2))).1 := by
  obtain ⟨saved,post,final,post2,final2,one,two⟩ := SCG_AcceptedPair.replies c hashv copy allocator id a H success
  obtain ⟨allocated1,reserved1,_⟩ := SCH_WrapperFirst.body _ copy allocator _ _ final saved post H one
  obtain ⟨allocated2,reserved2,_⟩ := SCH_WrapperSecond.body _ allocator _ _ final2 post2 H two
  have firstLog : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1 =
      (eval H (SdkC_Oracle.program (body1 c hashv id (eval H a.first).2))).1 :=
    SCG_WrapperLog.first _ hashv copy allocator _ _ allocated1 reserved1 H
  have secondLog : (eval H (secondCode c hashv allocator id
      (eval H (a.second (eval H a.first).2 saved post final)).2)).1 =
      (eval H (SdkC_Oracle.program (body2 c hashv id
        (eval H (a.second (eval H a.first).2 saved post final)).2))).1 :=
    SCG_WrapperLog.second _ allocator _ _ allocated2 reserved2 H
  refine ⟨saved,post,final,?_⟩
  rw [SCE_Execution.accepted_eval c hashv copy allocator id a H saved post final one]
  simp only [firstLog,secondLog,List.append_assoc]

#print axioms chronological
end AspisR1.SCH_AccountLog
end
