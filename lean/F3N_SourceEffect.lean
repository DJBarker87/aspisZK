import SdkC_SourceLaws
import CheckpointBytes5Inputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SourceEffect
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect

theorem accepted {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : SdkC_Source.Code A) (out : A)
    (before : SdkC_Source.Log) (history : Log)
    (aligned : CheckpointBytes5Inputs.observe history=SdkC_Source.readLog before)
    (success : (SdkC_Source.run hashv code before).1=ok out) :
    ∃ after,run (SdkC_Source.dictionary hashv) () code history=ok (out,after) ∧
      CheckpointBytes5Inputs.observe after=SdkC_Source.readLog (SdkC_Source.run hashv code before).2 := by
  induction code generalizing before history with
  | done a=>
    cases success
    exact ⟨history,rfl,aligned⟩
  | step result next ih=>
    cases result with
    | fail e=>cases success
    | div=>cases success
    | ok a=>exact ih a before history aligned success
  | read parts next ih=>
    cases returned : hashv parts with
    | fail e=>simp only [SdkC_Source.run,returned] at success;cases success
    | div=>simp only [SdkC_Source.run,returned] at success;cases success
    | ok digest=>
      have alignNext : CheckpointBytes5Inputs.observe (history++[(parts,digest)])=
          SdkC_Source.readLog (before++[⟨parts,ok digest⟩]) := by
        simp only [CheckpointBytes5Inputs.observe,SdkC_Source.readLog,List.map_append,List.map_cons,
          List.map_nil,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
        exact congrArg (fun xs=>xs++[(AspisV8R19.SqueezeOracleBridge.flatten parts,
          AspisV8R19.SqueezeOracleBridge.decodeState digest)]) aligned
      obtain ⟨after,ran,logs⟩ := ih digest (before++[⟨parts,ok digest⟩]) (history++[(parts,digest)]) alignNext
        (by simpa only [SdkC_Source.run,returned] using success)
      exact ⟨after,by simpa only [run,SdkC_Source.dictionary,returned,bind_tc_ok] using ran,
        by simpa only [SdkC_Source.run,returned] using logs⟩

#print axioms accepted
end AspisR1.F3N_SourceEffect
end
