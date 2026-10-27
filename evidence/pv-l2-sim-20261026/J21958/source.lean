import R1Z.PV_L2_F5SparsePred
import R1Z.ProverCommitBasisCounter47
set_option autoImplicit false
namespace R1Z.PV_L2_F5SparseWidth
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def width : Nat → Array field.QM31 10#usize → U8 → Recorded U8
  | 0,_,left => if left=0#u8 then ⟨ok 0#u8,[.guard 110 left.val 0 true]⟩
    else ⟨.div,[.guard 110 left.val 0 false]⟩
  | fuel+1,point,left => if left=0#u8 then ⟨ok 0#u8,[.guard 110 left.val 0 true]⟩
    else do
      let _ ← operation (.guard 110 left.val 0 false) (ok ())
      let n := U8.wrapping_sub left 1#u8
      let index := core.convert.num.FromUsizeU8.from n
      let value ← operation (.index 0 index.val) (Array.index_usize point index)
      let b ← PV_L2_F5SparsePred.boolean value
      if b then width fuel point n else PV_L2_Record.pure left

theorem erases (fuel : Nat) (point : Array field.QM31 10#usize) (left : U8)
    (enough : left.val≤fuel) :
    (width fuel point left).value = sparse_scan50.width point left := by
  induction fuel generalizing left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [width,if_pos hz,sparse_scan50.width,if_pos hz]
  | succ fuel ih =>
    by_cases hz : left=0#u8
    · rw [width,if_pos hz,sparse_scan50.width,if_pos hz]
    · have hpos : 0<left.val := by scalar_tac
      have hdec : (U8.wrapping_sub left 1#u8).val≤fuel := by
        rw [ProverCommitBasisCounter47.sub_one left hpos]
        omega
      rw [width,if_neg hz,sparse_scan50.width,if_neg hz]
      simp only [PV_L2_RecordCompact.bind_value,operation_value,
        PV_L2_F5SparsePred.boolean_erases,PV_L2_Record.pure_value,lift,bind_tc_ok,
        apply_ite,ih _ hdec]

theorem source_width (point : Array field.QM31 10#usize) :
    (width 10 point 10#u8).value = sparse_scan50.width point 10#u8 :=
  erases 10 point 10#u8 (by decide)

#print axioms erases
#print axioms source_width
end R1Z.PV_L2_F5SparseWidth
