import LPt_PreparedClaim
set_option autoImplicit false
namespace AspisR1.LPt_Nonvacuity
open Aeneas Aeneas.Std Result

def compact : Slice U8 := ⟨List.replicate 464 (0#u8),by rw [List.length_replicate]; scalar_tac⟩
def initial : Slice U8 := ⟨List.replicate 928 (0#u8),by rw [List.length_replicate]; scalar_tac⟩

theorem checked : LPt_External.compact.check_values compact=ok (.Ok ()) := by
  apply (LPt_LPl_C.Check.caller_iff compact (by change (List.replicate 464 (0#u8)).length=464; rw [List.length_replicate])).mpr
  intro row hr
  rw [←LPt_LPl.Check.stage]
  change LPt_LPl.Check.chunk (((List.replicate 464 (0#u8)).drop (16*row)).take 16)=true
  have size : min 16 (464-16*row)=16 := by omega
  simpa only [List.drop_replicate,List.take_replicate,size] using LPt_LPl.Check.zero_chunk

/-- A concrete byte-domain inhabitant, built using symbolic row bounds and
inherited zero-chunk/producer theorems, without enumerating the full buffer. -/
theorem expanded : ∃ y1 : Slice U8,
    LPt_LPn.Expand.NativeTrace compact.val initial.val 29 y1.val ∧
    LPt_External.compact.expand_values compact initial=ok (.Ok (),y1) ∧
    LPq_SelectedDomain.ByteDomain y1 := by
  have len : compact.val.length=464 := by change (List.replicate 464 (0#u8)).length=464; rw [List.length_replicate]
  have size : initial.val.length=928 := by change (List.replicate 928 (0#u8)).length=928; rw [List.length_replicate]
  obtain ⟨y1,trace,_,_,result⟩ := LPt_LPs_ProducerTotal.expansion compact initial len size
  exact ⟨y1,trace,result,LPt_ByteDomain.checked_expanded compact initial y1 len size checked trace⟩

#print axioms checked
#print axioms expanded
end AspisR1.LPt_Nonvacuity
