import ARQ_FirstTrace
import ARQ_FirstBody
import ARQ_SecondTrace
import ARQ_SecondBody
import SCG_AcceptedPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AccountChildren
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment SCE_Execution

/-- Both ideal outer traces are constructed on the accepted account's actual
response-selected inputs. This is the full chronology, with second-choice
queries retained at their original position. No native successes, syscall
inversion or standalone-source acceptance occur in the premises. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (success : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ saved post final post2 final2 log1 log2,
      let i := (eval H a.first).2
      let j := (eval H (a.second i saved post final)).2
      (eval H (firstCode c hashv copy allocator id i)).2 = ok (.Ok (saved,post,final)) ∧
      (eval H (secondCode c hashv allocator id j)).2 = ok (.Ok (post2,final2)) ∧
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H)
        (S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
          S2W_Outer.traceEffects id i.entry.first i.data) [] = ok (.Ok saved,log1) ∧
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H)
        (S2W_Outer.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
          S2W_Outer.traceEffects id (j.entry.second secondSizes) j.data j.slot) [] = ok (.Ok (),log2) ∧
      (eval H (account c hashv copy allocator id a)).1 = (eval H a.first).1 ++
        (ARQ_LowerTrace.trace c hashv H log1 ++
          ((eval H (a.second i saved post final)).1 ++ ARQ_LowerTrace.trace c hashv H log2)) := by
  obtain ⟨saved,post,final,post2,final2,first,second⟩ :=
    SCG_AcceptedPair.replies c hashv copy allocator id a H success
  obtain ⟨log1,ran1,same1⟩ := ARQ_FirstBody.accepted c hashv copy allocator id _ saved post final H first
  obtain ⟨log2,ran2,same2⟩ := ARQ_SecondBody.accepted c hashv allocator id _ post2 final2 H second
  refine ⟨saved,post,final,post2,final2,log1,log2,first,second,ran1,ran2,?_⟩
  rw [accepted_eval c hashv copy allocator id a H saved post final first,same1,same2]

#print axioms accepted
end AspisR1.ARQ_AccountChildren
end
