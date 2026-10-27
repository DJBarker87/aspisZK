import ARU_Returning
import GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_ReadHead
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge FS2.Duplex

theorem issued {A : Type} (hashv : Parts → Result Digest) (parts : Parts)
    (next : Digest → Code A) (value : A)
    (success : (run hashv (.read parts next) []).1 = ok value) :
    Read (readLog (run hashv (.read parts next) []).2) (flatten parts) := by
  cases called : hashv parts with
  | fail error => simp only [run,called] at success; cases success
  | div => simp only [run,called] at success; cases success
  | ok digest =>
    have extension :=  prefix_preserved hashv (next digest) [⟨parts,ok digest⟩]
    obtain ⟨suffix,shape⟩ := extension
    simp only [run,called,List.nil_append]
    rw [shape,SdkC_Oracle.readLog_append]
    change flatten parts ∈ (readLog [⟨parts,ok digest⟩] ++ readLog suffix).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_left _ (by simp only [readLog,List.filterMap_cons,List.filterMap_nil,List.map_cons,List.map_nil,List.mem_singleton])

#print axioms issued
end AspisR1.ARU_ReadHead
end
