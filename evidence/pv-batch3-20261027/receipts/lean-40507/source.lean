import PV_B3_Copy_222_Funs
namespace PV_B3_MultilinearGuard222
open Aeneas Aeneas.Std Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

theorem wrong_length (column : Slice Q) (point : Array Q 10#usize)
    (h : Slice.len column ≠ 1024#usize) :
    host_multilinear.multilinear_evaluate_qm31 column point = ok none := by
  simp [host_multilinear.multilinear_evaluate_qm31, h]

def emptyColumn : Slice Q := ⟨[], by decide⟩

theorem nonvacuity (point : Array Q 10#usize) :
    host_multilinear.multilinear_evaluate_qm31 emptyColumn point = ok none :=
  wrong_length emptyColumn point (by decide)

#print axioms wrong_length
#print axioms emptyColumn
#print axioms nonvacuity
end PV_B3_MultilinearGuard222
