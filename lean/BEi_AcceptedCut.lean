import BEi_BatchPrefix
import SdkC_BatchPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_AcceptedCut
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- A successful source result constructs an operational execution with the
original carrier and history. This is an interpreter existence theorem;
it is deliberately not called physical-runtime non-vacuity. -/
theorem construct {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (code : Code A) (value : A) (accepted : (SdkC_Source.run hashv code []).1 = .ok value)
    (state : S) (before : Log) :
    ∃ after log,
      Executes call code state before (.ok value) after log ∧
      log = before ++ (SdkC_Source.run hashv code []).2 := by
  have same : (BEf_Carrier.run call code state before).1 = .ok value :=
    (congrArg Prod.fst (BEf_Carrier.source call hashv binding code state before)).trans
      ((SdkC_Source.erasure hashv code before).trans ((SdkC_Source.erasure hashv code []).symm.trans accepted))
  have steps := BEi_ExecutionComplete.complete call code state before
  rw [same] at steps
  refine ⟨_,_,steps,?_⟩
  obtain ⟨retained,delta⟩ := BEi_RecorderCut.exact_cut call code state _ before _ (.ok value) steps
  rw [retained,BEi_RecorderCut.source_cut call hashv binding code state _ before _ (.ok value) steps]

#print axioms construct
end AspisR1.BEi_AcceptedCut
end
