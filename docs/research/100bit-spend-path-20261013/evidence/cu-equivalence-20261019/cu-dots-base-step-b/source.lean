import AspisR1CuDots.Funs
import CuSavingsDotsReads
import CuSavingsLoopRelation

/-! Prefix invariance of the actual emitted base-dot range loop. The proof
retains checked arithmetic, decoder failures and arbitrary shared arithmetic.
The source iterator discharges every term bound used by the read theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsDotsBaseStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuDots
open CuSavingsPrefix CuSavingsDotsReads CuSavingsLoopRelation
open OccupancyRangeTraversal
variable [Arithmetic]

local notation "baseBody" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body
local notation "baseLoop" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

theorem body_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (sums : Array U64 8#usize)
    (hs : slot.val < 4) (hend : iter.end.val ≤ 26) :
    baseBody (prefixArray bytes h).to_slice gamma slot iter sums =
      baseBody bytes gamma slot iter sums := by
  by_cases halt : iter.start.val ≥ iter.end.val
  · have hn := next_done iter halt
    simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,
      hn,bind_tc_ok]
  · obtain ⟨next,hn,hinc,hend1,_⟩ := next_step iter (by omega)
    simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,
      hn,bind_tc_ok]
    exact base_cont bytes h slot iter.start hs (by omega) _

#print axioms body_eq
end AspisR1.CuSavingsDotsBaseStep
