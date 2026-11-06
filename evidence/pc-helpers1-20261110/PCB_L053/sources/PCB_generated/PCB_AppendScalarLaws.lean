import PCB_AppendRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_AppendScalarLaws

theorem geometry (filled : U16) (offset : Usize)
    (cap : filled.val + offset.val < 256) :
    PCB_AppendRef.geometry filled offset =
      ok (Usize.ofNat (64 + 32 * (filled.val + offset.val))) := by
  unfold PCB_AppendRef.geometry
  scalar_tac

theorem filled (n : U16) (count : Usize)
    (cap : n.val + count.val ≤ 256) :
    PCB_AppendRef.filled_bytes n count =
      ok (core.num.U16.to_le_bytes (U16.ofNat (n.val + count.val))) := by
  unfold PCB_AppendRef.filled_bytes
  scalar_tac

#print axioms geometry
#print axioms filled
end PCB_AppendScalarLaws
