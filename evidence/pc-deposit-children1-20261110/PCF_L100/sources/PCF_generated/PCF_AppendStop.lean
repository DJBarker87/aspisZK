import PCF_Iterator
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace PCF_AppendStop
theorem stopped (header : PCB_AppendFullRef.RootPageHeaderV1)
    (roots : Slice (Array U32 8#usize)) (i : Nat) (count : Usize) (data : Slice U8)
    (stop : roots.length ≤ i) :
    PCB_AppendFullRef.append_ref_loop.body header (PCF_Iterator.cursor roots i count) data =
      ok (done (data,header)) := by
  simp only [PCB_AppendFullRef.append_ref_loop.body,PCF_Iterator.done roots i count stop,bind_tc_ok]
  rfl
#print axioms stopped
end PCF_AppendStop
