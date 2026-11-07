import NNG_LIBRecords
import LIB_VRecordDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRecordReached
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport

theorem getter (p : LIB_VCarriers.Prefix) (row : U8) (r : r1_wire.ValidatedRecord)
    (returned : NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) row = .ok (.Ok r)) :
    LIB_VRecords.validatedRecord p row.val = .ok (toT14 r) := by
  have same := NNG_LIBRecords.record p row
  rw [returned] at same
  exact (Result.ok.inj same).symm
#print axioms getter

/-- Reached getters establish decoder domains. These are internal source
facts, never extra finishInputDom or caller-success hypotheses. -/
theorem extra (p : LIB_VCarriers.Prefix) (r : r1_wire.ValidatedRecord)
    (returned : NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) 25#u8 = .ok (.Ok r)) :
    LIB_VDecode.Domain (toT14 r) 87 := by
  have same := getter p 25#u8 r returned
  obtain ⟨selected,field,domain⟩ := LIB_VRecordDomains.extra p
  have equal := Except.ok.inj (same.symm.trans field)
  rw [equal]
  exact domain
#print axioms extra

theorem beforeZ1 (p : LIB_VCarriers.Prefix) (r : r1_wire.ValidatedRecord)
    (returned : NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) 26#u8 = .ok (.Ok r)) :
    LIB_VDecode.Domain (toT14 r) 0 := by
  have same := getter p 26#u8 r returned
  obtain ⟨selected,field,domain⟩ := LIB_VRecordDomains.beforeZ1 p
  have equal := Except.ok.inj (same.symm.trans field)
  rw [equal]
  exact domain
#print axioms beforeZ1
end AspisR1.NNG_LIBRecordReached
