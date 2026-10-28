import PV_L2C_BlockRange
import R0Z.WriterRefineOccRow
set_option autoImplicit false
namespace PV_L2C_OccRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

structure Fields (o : R0WriterCopies.OccRecord) : Prop where
  occupied : o.occupied.val < 2147483647
  inverse : o.inverse.val < 2147483647
  commitment : Canon8 o.commitment
  selected : o.has_selected = true → o.selected.val < 2147483647

theorem cell (o : R0WriterCopies.OccRecord) (ho : Fields o) (c : Nat) (d : U32)
    (hd : d.val < 2147483647) : ((occRowCell o c).getD d).val < 2147483647 := by
  unfold occRowCell
  split_ifs with h0 h1 h2 h3
  · exact ho.occupied
  · exact ho.inverse
  · exact ho.commitment (c-2) (by omega)
  · exact ho.selected h3.2
  · exact hd
#print axioms cell

theorem row (buf : Array U32 256#usize) (hbuf : Canonical buf)
    (r : Usize) (hr : r.val ≤ 15) (o : R0WriterCopies.OccRecord) (ho : Fields o)
    (out : Array U32 256#usize) (hout : R0WriterCopies.write_occupancy_row buf r o = ok out) :
    Canonical out := by
  obtain ⟨expected,he,hcells⟩ := occ_row buf r hr o
  have same : out = expected := Result.ok.inj (hout.symm.trans he)
  intro k hk
  rw [same,hcells]
  split_ifs
  · exact cell o ho _ _ (hbuf k hk)
  · exact hbuf k hk
#print axioms row
end PV_L2C_OccRange
