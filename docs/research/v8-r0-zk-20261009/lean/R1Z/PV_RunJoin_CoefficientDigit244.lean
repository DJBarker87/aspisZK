import R1Z.PV_RunJoin_CoefficientRange44
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientDigit244
open Aeneas Aeneas.Std Result ProverRwSuccessCoefficientsSource

def digit (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 4#u32 &&& 3#usize) 4#u32

theorem body (j out : Usize) :
    transport.Variant.row_loop.body j { start := 2#usize, «end» := 5#usize } out =
      .ok (.cont ({ start := 3#usize, «end» := 5#usize },out ||| digit j)) := by
  have inc : Usize.wrapping_add 2#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_MergeLoop35.increment 2#usize (by decide)]
    rfl
  have hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 2#usize, «end» := 5#usize } =
      .ok (some 2#usize,{ start := 3#usize, «end» := 5#usize }) := by
    simpa only [PV_RunJoin_CoefficientRange44.next,PV_RunJoin_CoefficientRange44.between,
      PV_RunJoin_CoefficientRange44.advance,inc] using
      PV_RunJoin_CoefficientRange44.next_step 2#usize 5#usize (by decide)
  have lo : (2#usize * 2#usize : Result Usize) = .ok 4#usize := by scalar_tac
  have hi : (2#usize * 2#usize : Result Usize) = .ok 4#usize := by scalar_tac
  have tau : Array.index_usize transport.TAU 2#usize = .ok 2#usize := by rfl
  unfold transport.Variant.row_loop.body
  rw [hn]
  simp only [bind_tc_ok,lo]
  rw [PV_RunJoin_CheckedShift44.right j 4#usize (by decide)]
  simp only [bind_tc_ok,lift,tau,hi]
  rw [PV_RunJoin_CheckedShift44.left _ 4#usize (by decide)]
  simp only [bind_tc_ok,lift,digit]
  rfl
#print axioms body
end R1Z.PV_RunJoin_CoefficientDigit244
