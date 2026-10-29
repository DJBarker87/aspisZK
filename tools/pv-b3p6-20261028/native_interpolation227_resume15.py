from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean')
s='''import PV_B3P_InterpolationStep15227
import PV_B3P_SelectIndex227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def interpolation_native_limb15 (weights : Array aspis_core.field.QM31 3#usize)
    (column0 column1 column2 : Array U32 16#usize) (lane : Usize)
    (project : aspis_core.field.QM31 → U32) : Result U32 := do
  let w0 ← Array.index_usize weights 0#usize
  let w1 ← Array.index_usize weights 1#usize
  let w2 ← Array.index_usize weights 2#usize
  let c0 ← Array.index_usize column0 lane
  let c1 ← Array.index_usize column1 lane
  let c2 ← Array.index_usize column2 lane
  reference_poseidon.interpolate_three_constant_limb (project w0) (project w1) (project w2) c0 c1 c2

/-- The deployed constructor evaluates all six array reads separately for each
of its four component expressions. No cached-read assumption is needed. -/
def interpolation_native_value15 (weights : Array aspis_core.field.QM31 3#usize)
    (column0 column1 column2 : Array U32 16#usize) (lane : Usize) : Result aspis_core.field.QM31 := do
  let a ← interpolation_native_limb15 weights column0 column1 column2 lane (fun q => q.c0.a)
  let b ← interpolation_native_limb15 weights column0 column1 column2 lane (fun q => q.c0.b)
  let c0 ← aspis_core.field.CM31.new a b
  let c ← interpolation_native_limb15 weights column0 column1 column2 lane (fun q => q.c1.a)
  let d ← interpolation_native_limb15 weights column0 column1 column2 lane (fun q => q.c1.b)
  let c1 ← aspis_core.field.CM31.new c d
  .ok { c0 := c0, c1 := c1 }

attribute [local irreducible] reference_poseidon.interpolate_three_constant_limb
  aspis_core.field.CM31.new Array.update

theorem interpolation_native_value_binding15 (weights : Array aspis_core.field.QM31 3#usize)
    (column0 column1 column2 : Array U32 16#usize) (lane : Usize) (bound : lane.val < 16) :
    interpolation_native_value15 weights column0 column1 column2 lane =
      (do
        let c0 ← Array.index_usize column0 lane
        let c1 ← Array.index_usize column1 lane
        let c2 ← Array.index_usize column2 lane
        reference_poseidon.interpolate_column227 weights c0 c1 c2) := by
  have w0 := PV_B3P_SelectIndex227.index_value weights 0#usize (by decide)
  have w1 := PV_B3P_SelectIndex227.index_value weights 1#usize (by decide)
  have w2 := PV_B3P_SelectIndex227.index_value weights 2#usize (by decide)
  have c0 := PV_B3P_SelectIndex227.index_value column0 lane bound
  have c1 := PV_B3P_SelectIndex227.index_value column1 lane bound
  have c2 := PV_B3P_SelectIndex227.index_value column2 lane bound
  simp only [interpolation_native_value15,interpolation_native_limb15,
    reference_poseidon.interpolate_column227,w0,w1,w2,c0,c1,c2,bind_tc_ok,
    PV_B3P_Ordered227.bind_assoc]
#print axioms interpolation_native_value_binding15
end PV_B3P_Native15227
'''
(L/'PV_B3P_InterpolationNativeReads15227.lean').write_text(s)
