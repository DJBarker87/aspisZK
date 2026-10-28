import R1Z.PV_RunJoin_PolyCell38
import R1Z.PV_RunJoin_ZeroWord40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyCompact40
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PolyCell38
variable [ExternalTypes]

/-- A source polynomial cell has exactly sixteen zero high bytes, even when
its raw input requires the normalization performed by from_qm31. Only this
fixed 16-byte zero suffix is reduced, not a polynomial or field recurrence. -/
theorem high_half (q : Q) : (cell q).drop 16=List.replicate 16 (0#u8) := by
  simp only [cell,PV_RunJoin_FlatBytes35.wire,wide,Array.make,
    List.drop_succ_cons,List.drop_zero]
  simp only [PV_RunJoin_FlatBytes35.byte,PV_RunJoin_ZeroWord40.bytes,
    List.getElem_cons_zero,List.getElem_cons_succ]
  rfl

theorem split (q : Q) : cell q=(cell q).take 16 ++ List.replicate 16 (0#u8) := by
  rw [← high_half q]
  exact (List.take_append_drop 16 (cell q)).symm

#print axioms high_half
#print axioms split
end R1Z.PV_RunJoin_PolyCompact40
