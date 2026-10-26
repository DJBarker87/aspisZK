import R1Z.PV_L2_F5SparseWidth
import AspisR1ProducerRelease47.Sparse50
set_option autoImplicit false
namespace R1Z.PV_L2_F5SparseWeight
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def factor (value : field.QM31) (bit : Usize) : Recorded field.QM31 :=
  if bit=0#usize then operation (.guard 112 bit.val 0 true)
    (field.QM31.sub field.QM31.ONE value)
  else operation (.guard 112 bit.val 0 false) (ok value)

theorem factor_erases (value : field.QM31) (bit : Usize) :
    (factor value bit).value = sparse50.factor value bit := by
  by_cases hz : bit=0#usize <;> simp only [factor,sparse50.factor,hz,if_true,if_false,operation_value]

/-- Fixed-latency field calls are tagged by site, without exposing their
operands. Their compiled constant-time association remains V368. -/
def weight : Nat → Array field.QM31 10#usize → Usize → U8 → Usize → U8 →
    field.QM31 → Recorded field.QM31
  | 0,_,_,_,_,left,acc => if left=0#u8 then ⟨ok acc,[.guard 113 left.val 0 true]⟩
    else ⟨.div,[.guard 113 left.val 0 false]⟩
  | fuel+1,point,prefix1,width,index,left,acc =>
    if left=0#u8 then ⟨ok acc,[.guard 113 left.val 0 true]⟩ else do
      let _ ← operation (.guard 113 left.val 0 false) (ok ())
      let i1 := core.convert.num.FromUsizeU8.from width
      let i2 := core.num.Usize.wrapping_sub i1 1#usize
      let shift := core.num.Usize.wrapping_sub i2 index
      let i3 := UScalar.cast .U32 shift
      let i4 := core.num.Usize.wrapping_shr prefix1 i3
      let bit := i4 &&& 1#usize
      let value ← operation (.index 0 index.val) (Array.index_usize point index)
      let factor1 ← factor value bit
      let next := core.num.Usize.wrapping_add index 1#usize
      let remaining := U8.wrapping_sub left 1#u8
      let q ← operation (.guard 114 index.val width.val true) (field.QM31.mul acc factor1)
      weight fuel point prefix1 width next remaining q

theorem erases (fuel : Nat) (point : Array field.QM31 10#usize) (prefix1 : Usize)
    (width : U8) (index : Usize) (left : U8) (acc : field.QM31)
    (enough : left.val≤fuel) :
    (weight fuel point prefix1 width index left acc).value =
      sparse50.weight point prefix1 width index left acc := by
  induction fuel generalizing index left acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [weight,if_pos hz,sparse50.weight,if_pos hz]
  | succ fuel ih =>
    by_cases hz : left=0#u8
    · rw [weight,if_pos hz,sparse50.weight,if_pos hz]
    · have hpos : 0<left.val := by scalar_tac
      have hdec : (U8.wrapping_sub left 1#u8).val≤fuel := by
        rw [ProverCommitBasisCounter47.sub_one left hpos]
        omega
      rw [weight,if_neg hz,sparse50.weight,if_neg hz]
      simp only [PV_L2_RecordCompact.bind_value,operation_value,factor_erases,
        lift,bind_tc_ok,ih _ _ _ hdec]

#print axioms factor_erases
#print axioms erases
end R1Z.PV_L2_F5SparseWeight
