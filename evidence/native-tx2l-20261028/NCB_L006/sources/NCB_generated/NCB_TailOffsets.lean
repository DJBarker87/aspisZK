import NBS_DotTail
import FJi_TailInputs
set_option autoImplicit false
noncomputable section
namespace NCB_TailOffsets
open Aeneas Aeneas.Std Result AspisR1

def slot (s : Fin 4) : Usize := Usize.ofNat s.val (by have:=s.isLt;scalar_tac)

theorem first (q : Array U8 608#usize) (s : Fin 4) :
    FJi_TailInputs.read0 q (slot s)=JFr_TX2_TailRead.read q
      (JFr_TX2_Tails.offset s 0) (JFr_TX2_Tails.stop s 0) := by
  let base : Usize := Usize.ofNat (s.val*120) (by have:=s.isLt;scalar_tac)
  have mul : slot s*120#usize=ok base :=
    Port4A_ReaderInstall.mul_value _ _ (by change s.val*120≤65536;have:=s.isLt;omega)
  have add : base+104#usize=ok (JFr_TX2_Tails.offset s 0) := by
    have h := Port4A_ReaderInstall.add_value base 104#usize (by change s.val*120+104≤65536;have:=s.isLt;omega)
    simpa only [JFr_TX2_Tails.offset,JFr_TX2_Tails.start,Fin.val_zero,if_pos rfl,base,Nat.mul_comm] using h
  have stop : base+120#usize=ok (JFr_TX2_Tails.stop s 0) := by
    have h := Port4A_ReaderInstall.add_value base 120#usize (by change s.val*120+120≤65536;have:=s.isLt;omega)
    simpa only [JFr_TX2_Tails.stop,JFr_TX2_Tails.start,Fin.val_zero,if_pos rfl,base,Nat.mul_comm,Nat.add_assoc] using h
  simp only [FJi_TailInputs.read0,mul,add,stop,bind_tc_ok,JFr_TX2_TailRead.read]
#print axioms first
end NCB_TailOffsets
end
