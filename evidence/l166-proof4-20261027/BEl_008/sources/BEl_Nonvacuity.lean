import BEl_RawBackend
import BEk_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

/-- Positive-query reference model: two duplicate attempts survive rejection,
and the live backend state changes on each actual returned call. This is
not a real-byte successful native batch fixture or joint root realization. -/
theorem rejected (parts : Parts) (digest : Digest) (n : Nat) (before : Log) :
    let code : Code (core.result.Result Unit Unit) :=
      .read parts (fun _ => .read parts (fun _ => .done (.Err ())))
    BEl_RawBackend.run (fun _ state => (digest,state+1)) code n
      (BEl_Recorder.completed before) =
      (.ok (.Err ()),n+1+1,
       BEl_Recorder.completed ((before ++ [⟨parts,.ok digest⟩]) ++ [⟨parts,.ok digest⟩])) := by
  simp only [BEl_RawBackend.run,←BEl_Recorder.completed_append]

/-- Every completed source occurrence is retained separately in the wrapper. -/
theorem occurrences (before : Log) (parts : Parts) (digest : Digest) :
    (BEl_Recorder.complete
      (BEl_Recorder.complete (BEl_Recorder.completed before) parts (.ok digest))
      parts (.ok digest)).length = before.length + 2 := by
  simp only [BEl_Recorder.complete,BEl_Recorder.completed,List.length_append,
    List.length_cons,List.length_nil,List.length_map]
  omega

#print axioms rejected
#print axioms occurrences
end AspisR1.BEl_Nonvacuity
end
