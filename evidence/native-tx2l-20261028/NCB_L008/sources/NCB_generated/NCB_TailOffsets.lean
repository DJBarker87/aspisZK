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
    exact h.trans (congrArg Result.ok (by
      apply UScalar.eq_of_val_eq
      change s.val*120+104=JFr_TX2_Tails.start s 0
      simp [JFr_TX2_Tails.start,Nat.mul_comm]))
  have stop : base+120#usize=ok (JFr_TX2_Tails.stop s 0) := by
    have h := Port4A_ReaderInstall.add_value base 120#usize (by change s.val*120+120≤65536;have:=s.isLt;omega)
    exact h.trans (congrArg Result.ok (by
      apply UScalar.eq_of_val_eq
      change s.val*120+120=JFr_TX2_Tails.start s 0+16
      simp [JFr_TX2_Tails.start,Nat.mul_comm,Nat.add_assoc]))
  simp only [FJi_TailInputs.read0,mul,add,stop,bind_tc_ok,JFr_TX2_TailRead.read]

theorem second (q : Array U8 608#usize) (s : Fin 4) :
    FJi_TailInputs.read1 q (slot s)=JFr_TX2_TailRead.read q
      (JFr_TX2_Tails.offset s 1) (JFr_TX2_Tails.stop s 1) := by
  let delta : Usize := Usize.ofNat (s.val*32) (by have:=s.isLt;scalar_tac)
  let base : Usize := Usize.ofNat (480+s.val*32) (by have:=s.isLt;scalar_tac)
  have mul : slot s*32#usize=ok delta :=
    Port4A_ReaderInstall.mul_value _ _ (by change s.val*32≤65536;have:=s.isLt;omega)
  have add : 480#usize+delta=ok base :=
    Port4A_ReaderInstall.add_value _ _ (by change 480+s.val*32≤65536;have:=s.isLt;omega)
  have small : (0#usize*16#usize : Result Usize)=ok 0#usize := Port4A_ReaderInstall.mul_value _ _ (by decide)
  have start : base+0#usize=ok (JFr_TX2_Tails.offset s 1) := by
    have h := Port4A_ReaderInstall.add_value base 0#usize (by change 480+s.val*32+0≤65536;have:=s.isLt;omega)
    exact h.trans (congrArg Result.ok (by
      apply UScalar.eq_of_val_eq
      change 480+s.val*32+0=JFr_TX2_Tails.start s 1
      simp [JFr_TX2_Tails.start,Nat.mul_comm]))
  have stop : JFr_TX2_Tails.offset s 1+16#usize=ok (JFr_TX2_Tails.stop s 1) := by
    apply Port4A_ReaderInstall.add_value
    change JFr_TX2_Tails.start s 1+16≤65536
    simp [JFr_TX2_Tails.start]
    have:=s.isLt
    omega
  simp only [FJi_TailInputs.read1,mul,add,small,start,stop,bind_tc_ok,JFr_TX2_TailRead.read]

theorem third (q : Array U8 608#usize) (s : Fin 4) :
    FJi_TailInputs.read2 q (slot s)=JFr_TX2_TailRead.read q
      (JFr_TX2_Tails.offset s 2) (JFr_TX2_Tails.stop s 2) := by
  let delta : Usize := Usize.ofNat (s.val*32) (by have:=s.isLt;scalar_tac)
  let base : Usize := Usize.ofNat (480+s.val*32) (by have:=s.isLt;scalar_tac)
  have mul : slot s*32#usize=ok delta :=
    Port4A_ReaderInstall.mul_value _ _ (by change s.val*32≤65536;have:=s.isLt;omega)
  have add : 480#usize+delta=ok base :=
    Port4A_ReaderInstall.add_value _ _ (by change 480+s.val*32≤65536;have:=s.isLt;omega)
  have small : (1#usize*16#usize : Result Usize)=ok 16#usize := Port4A_ReaderInstall.mul_value _ _ (by decide)
  have start : base+16#usize=ok (JFr_TX2_Tails.offset s 2) := by
    have h := Port4A_ReaderInstall.add_value base 16#usize (by change 480+s.val*32+16≤65536;have:=s.isLt;omega)
    exact h.trans (congrArg Result.ok (by
      apply UScalar.eq_of_val_eq
      change 480+s.val*32+16=JFr_TX2_Tails.start s 2
      simp [JFr_TX2_Tails.start,Nat.mul_comm]))
  have stop : JFr_TX2_Tails.offset s 2+16#usize=ok (JFr_TX2_Tails.stop s 2) := by
    apply Port4A_ReaderInstall.add_value
    change JFr_TX2_Tails.start s 2+16≤65536
    simp [JFr_TX2_Tails.start]
    have:=s.isLt
    omega
  simp only [FJi_TailInputs.read2,mul,add,small,start,stop,bind_tc_ok,JFr_TX2_TailRead.read]

#print axioms first
#print axioms second
#print axioms third
end NCB_TailOffsets
end
