import R1Z.PV_L2_F5SparseWidth
set_option autoImplicit false
namespace R1Z.PV_L2_F5SparseSuffix
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def suffix : Nat → Array field.QM31 10#usize → Usize → U8 → Recorded Usize
  | 0,_,_,left => if left=0#u8 then ⟨ok 0#usize,[.guard 111 left.val 0 true]⟩
    else ⟨.div,[.guard 111 left.val 0 false]⟩
  | fuel+1,point,start,left => if left=0#u8 then ⟨ok 0#usize,[.guard 111 left.val 0 true]⟩
    else do
      let _ ← operation (.guard 111 left.val 0 false) (ok ())
      let n := U8.wrapping_sub left 1#u8
      let prev ← suffix fuel point start n
      let index := core.convert.num.FromUsizeU8.from n
      let at := core.num.Usize.wrapping_add start index
      let value ← operation (.index 0 at.val) (Array.index_usize point at)
      let shifted := core.num.Usize.wrapping_shl prev 1#u32
      let b ← PV_L2_F5SparsePred.one value
      let bit := core.convert.num.FromUsizeBool.from b
      PV_L2_Record.pure (shifted ||| bit)

theorem erases (fuel : Nat) (point : Array field.QM31 10#usize) (start : Usize)
    (left : U8) (enough : left.val≤fuel) :
    (suffix fuel point start left).value = sparse_scan50.suffix point start left := by
  induction fuel generalizing left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [suffix,if_pos hz,sparse_scan50.suffix,if_pos hz]
  | succ fuel ih =>
    by_cases hz : left=0#u8
    · rw [suffix,if_pos hz,sparse_scan50.suffix,if_pos hz]
    · have hpos : 0<left.val := by scalar_tac
      have hdec : (U8.wrapping_sub left 1#u8).val≤fuel := by
        rw [ProverCommitBasisCounter47.sub_one left hpos]
        omega
      rw [suffix,if_neg hz,sparse_scan50.suffix,if_neg hz]
      simp only [PV_L2_RecordCompact.bind_value,operation_value,
        PV_L2_F5SparsePred.one_erases,PV_L2_Record.pure_value,lift,bind_tc_ok,ih _ hdec]

#print axioms erases
end R1Z.PV_L2_F5SparseSuffix
