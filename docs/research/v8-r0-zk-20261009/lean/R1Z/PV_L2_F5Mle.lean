import R1Z.PV_L2_F5SparseSum
import R1Z.PV_L2_F5SparseSuffix
import AspisR1ProducerRelease47.Mle50
set_option autoImplicit false
namespace R1Z.PV_L2_F5Mle
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def suffix (point : Array field.QM31 10#usize) (start : Usize) (left : U8) :=
  PV_L2_F5SparseSuffix.suffix left.val point start left
theorem suffix_erases (point : Array field.QM31 10#usize) (start : Usize) (left : U8) :
    (suffix point start left).value = sparse_scan50.suffix point start left :=
  PV_L2_F5SparseSuffix.erases left.val point start left (Nat.le_refl _)

/-- Full owned MLE: all ZERO/ONE comparisons, address visits, loop stops
and field-call sites are retained. It does not claim native allocator cost
or native primitive timing; those remain in V357/V368. -/
def recorded (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize) :
    Recorded field.QM31 := do
  let width ← PV_L2_F5SparseWidth.width 10 point 10#u8
  let trailing := U8.wrapping_sub 10#u8 width
  let start := core.convert.num.FromUsizeU8.from width
  let suffix1 ← suffix point start trailing
  let count ← operation (.guard 119 width.val 0 true) (mle50.count width)
  PV_L2_F5SparseSum.run point column width trailing suffix1 0#usize count field.QM31.ZERO

theorem erases (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize) :
    (recorded point column).value = mle50.mle point column := by
  simp only [recorded,mle50.mle,PV_L2_RecordCompact.bind_value,
    PV_L2_F5SparseWidth.source_width,suffix_erases,operation_value,
    PV_L2_F5SparseSum.run_erases,lift,bind_tc_ok]

#print axioms suffix_erases
#print axioms erases
end R1Z.PV_L2_F5Mle
