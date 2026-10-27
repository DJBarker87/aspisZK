import R1Z.PV_L2_F5SparseWeight
import AspisR1ProducerRelease47.SparseSum50
import R1Z.ProverCommitPairCounter47
set_option autoImplicit false
namespace R1Z.PV_L2_F5SparseSum
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def sum : Nat → Array field.QM31 10#usize → Array field.QM31 1024#usize →
    U8 → U8 → Usize → Usize → U16 → field.QM31 → Recorded field.QM31
  | 0,_,_,_,_,_,_,left,acc => if left=0#u16 then ⟨ok acc,[.guard 115 left.val 0 true]⟩
    else ⟨.div,[.guard 115 left.val 0 false]⟩
  | fuel+1,point,column,width,trailing,suffix,pref,left,acc =>
    if left=0#u16 then ⟨ok acc,[.guard 115 left.val 0 true]⟩ else do
      let _ ← operation (.guard 115 left.val 0 false) (ok ())
      let weight ← PV_L2_F5SparseWeight.weight width.val point pref width 0#usize width field.QM31.ONE
      let row ← operation (.guard 116 pref.val trailing.val true) (sparse50.row pref trailing suffix)
      let value ← operation (.index 1 row.val) (Array.index_usize column row)
      let product ← operation (.guard 117 pref.val 0 true) (field.QM31.mul weight value)
      let next := core.num.Usize.wrapping_add pref 1#usize
      let remaining := U16.wrapping_sub left 1#u16
      let q ← operation (.guard 118 pref.val 0 true) (field.QM31.add acc product)
      sum fuel point column width trailing suffix next remaining q

theorem erases (fuel : Nat) (point : Array field.QM31 10#usize)
    (column : Array field.QM31 1024#usize) (width trailing : U8)
    (suffix pref : Usize) (left : U16) (acc : field.QM31) (enough : left.val≤fuel) :
    (sum fuel point column width trailing suffix pref left acc).value =
      sparse_sum50.sum point column width trailing suffix pref left acc := by
  induction fuel generalizing pref left acc with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    rw [sum,if_pos hz,sparse_sum50.sum,if_pos hz]
  | succ fuel ih =>
    by_cases hz : left=0#u16
    · rw [sum,if_pos hz,sparse_sum50.sum,if_pos hz]
    · have hpos : 0<left.val := by scalar_tac
      have hdec : (U16.wrapping_sub left 1#u16).val≤fuel := by
        rw [ProverCommitPairCounter47.sub_one left hpos]
        omega
      rw [sum,if_neg hz,sparse_sum50.sum,if_neg hz]
      simp only [PV_L2_RecordCompact.bind_value,operation_value,lift,bind_tc_ok,
        PV_L2_F5SparseWeight.erases width.val point pref width 0#usize width
          field.QM31.ONE (Nat.le_refl _),ih _ _ _ hdec]

def run (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize)
    (width trailing : U8) (suffix pref : Usize) (left : U16) (acc : field.QM31) :=
  sum left.val point column width trailing suffix pref left acc

theorem run_erases (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize)
    (width trailing : U8) (suffix pref : Usize) (left : U16) (acc : field.QM31) :
    (run point column width trailing suffix pref left acc).value =
      sparse_sum50.sum point column width trailing suffix pref left acc :=
  erases left.val point column width trailing suffix pref left acc (Nat.le_refl _)

#print axioms erases
#print axioms run_erases
end R1Z.PV_L2_F5SparseSum
