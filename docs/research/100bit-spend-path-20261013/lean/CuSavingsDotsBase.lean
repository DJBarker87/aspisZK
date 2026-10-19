import CuSavingsDotsBaseProgress

/-! Prefix invariance of the actual emitted base-dot range loop. The proof
retains checked arithmetic, decoder failures and arbitrary shared arithmetic.
The source iterator discharges every term bound used by the read theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsDotsBase
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuDots
open CuSavingsPrefix CuSavingsDotsReads CuSavingsLoopRelation
open OccupancyRangeTraversal
variable [Arithmetic]

local notation "baseBody" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body
local notation "baseLoop" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

theorem source_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (sums : Array U64 8#usize)
    (hs : slot.val < 4) (hend : iter.end.val ≤ 26) :
    baseLoop iter (prefixArray bytes h).to_slice gamma slot sums =
      baseLoop iter bytes gamma slot sums := by
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
  refine loop_eq
    (fun (iter1,sums1) => baseBody (prefixArray bytes h).to_slice gamma slot iter1 sums1)
    (fun (iter1,sums1) => baseBody bytes gamma slot iter1 sums1)
    (fun state => state.1.end.val ≤ 26)
    (fun state => state.1.end.val-state.1.start.val)
    ?_ ?_ (iter,sums) hend
  · intro state hi
    rcases state with ⟨it,acc⟩
    exact CuSavingsDotsBaseStep.body_eq bytes h gamma slot it acc hs hi
  · intro state next hi hc
    rcases state with ⟨it,acc⟩
    rcases next with ⟨it1,acc1⟩
    exact CuSavingsDotsBaseProgress.body_progress bytes gamma slot it acc hi
      (.cont (it1,acc1)) hc

#print axioms source_eq
end AspisR1.CuSavingsDotsBase
