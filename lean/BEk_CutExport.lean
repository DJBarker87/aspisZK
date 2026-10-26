import BEk_QueryPrefix
import BEj_SlotExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_CutExport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Same recorder cut as BEj; replace its global ideal-oracle premise by
agreement only at the computed successful attempts. Failed final attempts,
duplicates, pure errors, and arbitrary existing histories are retained.
The physical local law remains explicit and is NOT discharged here. -/
theorem queried {S A E F : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (H : Bytes → State) (code : Code (core.result.Result A F))
    (n : Nat) (count : GExp_CountLaws.count n code)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S A E)
    (law : BEh_Scope.Law native (BEf_Carrier.run call code state before))
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv code []).2) :
    native.2.2 = before ++ BEi_RecorderCut.issued before native.2.2 ∧
    BEi_RecorderCut.issued before native.2.2 = (SdkC_Source.run hashv code []).2 ∧
    (BEi_RecorderCut.issued before native.2.2).length ≤ n ∧
    ∃ remaining, (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
      RPx_AttemptPrefix.addresses (BEi_RecorderCut.issued before native.2.2) ++ remaining := by
  have cut := BEj_LocalExport.cut call hashv binding code state before native law
  obtain ⟨kept,remaining,same,ideal⟩ := BEk_QueryPrefix.transport code hashv H [] agrees
  simp only [RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append] at same
  have attempted : (SdkC_Source.run hashv code []).2.length ≤ n := by
    have lengths := congrArg List.length ideal
    simp only [List.length_map,List.length_append] at lengths
    have actual := congrArg List.length same
    simp only [List.length_map] at actual
    have bounded := count H
    omega
  exact ⟨cut.1,cut.2.1,by rw [cut.2.1]; exact attempted,
    ⟨remaining,by rw [cut.2.1]; exact ideal.trans (congrArg (· ++ remaining) same.symm)⟩⟩

#print axioms queried
end AspisR1.BEk_CutExport
end
