import R1Z.PV_RunJoin_CoefficientDigit044
import R1Z.PV_RunJoin_CoefficientDigit144
import R1Z.PV_RunJoin_CoefficientDigit244
import R1Z.PV_RunJoin_CoefficientDigit344
import R1Z.PV_RunJoin_CoefficientDigit444
import R1Z.PV_RunJoin_CoefficientRowMath44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientRow44
open Aeneas Aeneas.Std Result ProverRwSuccessCoefficientsSource

theorem stop (j out : Usize) :
    transport.Variant.row_loop.body j { start := 5#usize, «end» := 5#usize } out = .ok (.done out) := by
  have hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 5#usize, «end» := 5#usize } =
      .ok (none,{ start := 5#usize, «end» := 5#usize }) := by
    simpa only [PV_RunJoin_CoefficientRange44.next,PV_RunJoin_CoefficientRange44.between] using
      PV_RunJoin_CoefficientRange44.next_done 5#usize 5#usize (by decide)
  unfold transport.Variant.row_loop.body
  rw [hn]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]

def suffix5 (_ : Usize) (out : Usize) := out

theorem source5 (j out : Usize) :
    transport.Variant.row_loop { start := 5#usize, «end» := 5#usize } j out = .ok (suffix5 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [stop,bind_tc_ok,suffix5]

def suffix4 (j out : Usize) : Usize := suffix5 j (out ||| PV_RunJoin_CoefficientDigit444.digit j)
theorem source4 (j out : Usize) :
    transport.Variant.row_loop { start := 4#usize, «end» := 5#usize } j out = .ok (suffix4 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_CoefficientDigit444.body,bind_tc_ok]
  exact source5 j (out ||| PV_RunJoin_CoefficientDigit444.digit j)

def suffix3 (j out : Usize) : Usize := suffix4 j (out ||| PV_RunJoin_CoefficientDigit344.digit j)
theorem source3 (j out : Usize) :
    transport.Variant.row_loop { start := 3#usize, «end» := 5#usize } j out = .ok (suffix3 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_CoefficientDigit344.body,bind_tc_ok]
  exact source4 j (out ||| PV_RunJoin_CoefficientDigit344.digit j)

def suffix2 (j out : Usize) : Usize := suffix3 j (out ||| PV_RunJoin_CoefficientDigit244.digit j)
theorem source2 (j out : Usize) :
    transport.Variant.row_loop { start := 2#usize, «end» := 5#usize } j out = .ok (suffix2 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_CoefficientDigit244.body,bind_tc_ok]
  exact source3 j (out ||| PV_RunJoin_CoefficientDigit244.digit j)

def suffix1 (j out : Usize) : Usize := suffix2 j (out ||| PV_RunJoin_CoefficientDigit144.digit j)
theorem source1 (j out : Usize) :
    transport.Variant.row_loop { start := 1#usize, «end» := 5#usize } j out = .ok (suffix1 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_CoefficientDigit144.body,bind_tc_ok]
  exact source2 j (out ||| PV_RunJoin_CoefficientDigit144.digit j)

def suffix0 (j out : Usize) : Usize := suffix1 j (out ||| PV_RunJoin_CoefficientDigit044.digit j)
theorem source0 (j out : Usize) :
    transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j out = .ok (suffix0 j out) := by
  unfold transport.Variant.row_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_CoefficientDigit044.body,bind_tc_ok]
  exact source1 j (out ||| PV_RunJoin_CoefficientDigit044.digit j)

theorem shift_zero (x : Usize) (hx : x.val < 4) : Usize.wrapping_shl x 0#u32 = x := by
  apply UScalar.eq_of_val_eq
  rw [PV_CB3_WeightsMachine.shift_left x 0#u32 hx (by decide)]
  simp only [show (0#u32).val=0 from rfl,Nat.pow_zero,Nat.mul_one]

theorem shape (j : Usize) : suffix0 j 0#usize = PV_CB3_WeightsMachineRow.row j := by
  have z : 0#usize ||| PV_RunJoin_CoefficientDigit044.digit j = PV_RunJoin_CoefficientDigit044.digit j := by
    apply UScalar.eq_of_val_eq
    rw [PV_CB3_WeightsMachineRow.or_value]
    exact Nat.zero_or _
  unfold suffix0 suffix1 suffix2 suffix3 suffix4 suffix5
  rw [z]
  dsimp only [PV_RunJoin_CoefficientDigit044.digit,PV_RunJoin_CoefficientDigit144.digit,
    PV_RunJoin_CoefficientDigit244.digit,PV_RunJoin_CoefficientDigit344.digit,
    PV_RunJoin_CoefficientDigit444.digit,PV_CB3_WeightsMachineRow.row,PV_CB3_WeightsMachineRow.digit]
  rw [shift_zero _ (PV_CB3_WeightsMachineRow.digit_bound j 6#u32 (by decide))]

theorem row (v : transport.Variant) (j : Usize) :
    transport.Variant.row v j = .ok (PV_CB3_WeightsMachineRow.row j) := by
  unfold transport.Variant.row
  rw [source0,shape]
#print axioms stop
#print axioms source5
#print axioms source4
#print axioms source3
#print axioms source2
#print axioms source1
#print axioms source0
#print axioms shift_zero
#print axioms shape
#print axioms row
end R1Z.PV_RunJoin_CoefficientRow44
