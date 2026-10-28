import NCV_Install
set_option autoImplicit false
namespace NCV_Reject
open Aeneas Aeneas.Std Result

theorem master (b : Slice U8) (bad : b.val.length ≠ 384) :
    NCV_Reference.decode_master_ref b=ok (.Err ()) := by
  have h : (Slice.len b != 384#usize) = true := by scalar_tac
  unfold NCV_Reference.decode_master_ref
  rw [if_pos h]

theorem checkpoint (b : Slice U8) (bad : b.val.length ≠ 192) :
    NCV_Reference.decode_checkpoint_ref b=ok (.Err ()) := by
  have h : (Slice.len b != 192#usize) = true := by scalar_tac
  unfold NCV_Reference.decode_checkpoint_ref
  rw [if_pos h]

theorem lane (b : Slice U8) (bad : b.val.length ≠ 768) :
    NCV_Reference.decode_lane_ref b=ok (.Err ()) := by
  have h : (Slice.len b != 768#usize) = true := by scalar_tac
  unfold NCV_Reference.decode_lane_ref
  rw [if_pos h]

theorem op48 (b : Slice U8) (bad : b.val.length ≠ 384) :
    NCV_Install.op48 b=ok (.Err .InvalidAccountData) := by
  simp only [NCV_Install.op48,master b bad,bind_tc_ok,NCV_Install.mapReturn]

theorem op49 (b : Slice U8) (bad : b.val.length ≠ 192) :
    NCV_Install.op49 b=ok (.Err .InvalidAccountData) := by
  simp only [NCV_Install.op49,checkpoint b bad,bind_tc_ok,NCV_Install.mapReturn]

theorem op50 (b : Slice U8) (bad : b.val.length ≠ 768) :
    NCV_Install.op50 b=ok (.Err .InvalidAccountData) := by
  simp only [NCV_Install.op50,lane b bad,bind_tc_ok,NCV_Install.mapReturn]

#print axioms master
#print axioms checkpoint
#print axioms lane
#print axioms op48
#print axioms op49
#print axioms op50
end NCV_Reject
