import NNG_LIBRecordReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRecordFrame
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport

theorem circle_domain (p : LIB_VCarriers.Prefix) (slot : Fin 27) (r : r1_wire.ValidatedRecord)
    (returned : NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) (NJM_InvocationRoots.row slot) = .ok (.Ok r)) :
    (toT14 r).framed.val.length ≤ 3717 := by
  have same := NNG_LIBRecordReached.getter p (NJM_InvocationRoots.row slot) r returned
  change LIB_VRecords.validatedRecord p slot.val = .ok (toT14 r) at same
  obtain ⟨selected,field,tag,geometry⟩ := LIB_VRecordDomains.record p slot
  have equal := Except.ok.inj (same.symm.trans field)
  rw [equal,geometry]
  exact (NGX_PrefixGeometry.widths slot.val).2
#print axioms circle_domain

theorem payload2 (p : LIB_VCarriers.Prefix) (bytes : Slice U8)
    (returned : NNG_Install.payload (NNG_LIBData.lowerPrefix p) 2#u8 = .ok (.Ok bytes)) :
    bytes.val.length = 32 := by
  have same := NNG_LIBRecords.payload p 2#u8
  rw [returned] at same
  have field : LIB_VRecords.payload p 2 = .ok (LIB_Carriers.bytes bytes) := (Result.ok.inj same).symm
  obtain ⟨selected,model,length⟩ := LIB_VRecordDomains.payload2 p
  have equal := Except.ok.inj (field.symm.trans model)
  have selectedLength : (LIB_Carriers.bytes bytes).length = 32 := by
    rw [equal]
    exact length
  rw [NNG_LIBData.bytes_length] at selectedLength
  exact selectedLength
#print axioms payload2
end AspisR1.NNG_LIBRecordFrame
