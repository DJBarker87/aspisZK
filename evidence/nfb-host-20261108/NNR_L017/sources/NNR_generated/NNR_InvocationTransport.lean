import NNR_RecordTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_InvocationTransport
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (k : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem forward {X A : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (p : Program Event A) (result : Result A) (records : List (Occurrence (part H pda k r) d hash))
 (native : Invocation (part H pda k r) d hash p result records)
 (equal : ∀ o ∈ records, NLT_NativeWindows.window (part H pda k r) d hash o.entered o.input =
  NLT_NativeWindows.window H d hash o.entered o.input) :
 ∃ records' : List (Occurrence H d hash), Invocation H d hash p result records' ∧
 records'.map NLT_NativeInvocation.actual = records.map NLT_NativeInvocation.actual := by
 induction native with
 | ret value => exact ⟨[],.ret value,rfl⟩
 | prim_ok value next result records tail ih =>
  obtain ⟨rs,nt,eq⟩ := ih equal
  exact ⟨rs,.prim_ok value next result rs nt,eq⟩
 | prim_fail error next => exact ⟨[],.prim_fail error next,rfl⟩
 | prim_div next => exact ⟨[],.prim_div next,rfl⟩
 | call_ok codec seed next o same value decoded result records tail ih =>
  let o' := NNR_RecordTransport.record H pda k r o (equal o (by simp))
  have eqo := NNR_RecordTransport.actual H pda k r o (equal o (by simp))
  obtain ⟨rs,nt,eq⟩ := ih (fun x hx => equal x (by simp [hx]))
  refine ⟨o'::rs,.call_ok codec seed next o' same value ?_ result rs nt,?_⟩
  · rw [eqo]; exact decoded
  · simp only [List.map_cons,eqo,eq]
 | call_fail codec seed next o same error decoded =>
  let o' := NNR_RecordTransport.record H pda k r o (equal o (by simp))
  have eqo := NNR_RecordTransport.actual H pda k r o (equal o (by simp))
  refine ⟨[o'],.call_fail codec seed next o' same error ?_,?_⟩
  · rw [eqo]; exact decoded
  · simp only [List.map_cons,List.map_nil,eqo]
 | call_div codec seed next o same decoded =>
  let o' := NNR_RecordTransport.record H pda k r o (equal o (by simp))
  have eqo := NNR_RecordTransport.actual H pda k r o (equal o (by simp))
  refine ⟨[o'],.call_div codec seed next o' same ?_,?_⟩
  · rw [eqo]; exact decoded
  · simp only [List.map_cons,List.map_nil,eqo]
#print axioms forward
end AspisR1.NNR_InvocationTransport
end
