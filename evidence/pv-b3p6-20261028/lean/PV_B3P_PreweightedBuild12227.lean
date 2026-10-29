import PV_B3P_BindBranch12227
import PV_B3P_Ordered227
import PV_B3P_P227_08
import PV_B3P_FourStores12227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def preweighted_window12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (group_index slot : Usize) :
    Result aspis_core.field.QM31 := do
  let base ← lift (Usize.wrapping_mul 4#usize group_index)
  let source ← lift (Usize.wrapping_add base slot)
  if source >= start then
    let stop ← lift (Usize.wrapping_add start N)
    if source < stop then
      let offset ← lift (Usize.wrapping_sub source start)
      Array.index_usize values offset
    else .ok aspis_core.field.QM31.ZERO
  else .ok aspis_core.field.QM31.ZERO

def preweighted_build_stores12 {N : Usize} (start : Usize) (values : Array aspis_core.field.QM31 N)
    (group_index : Usize) : Result (Array aspis_core.field.QM31 4#usize) := do
  let output := Array.repeat 4#usize aspis_core.field.QM31.ZERO
  let i ← lift (Std.Usize.wrapping_mul 4#usize group_index)
  let source ← lift (Std.Usize.wrapping_add i 0#usize)
  let q ←
    if source >= start
    then
      do
      let i1 ← lift (Std.Usize.wrapping_add start N)
      if source < i1
      then
        let i2 ← lift (Std.Usize.wrapping_sub source start)
        Array.index_usize values i2
      else ok aspis_core.field.QM31.ZERO
    else ok aspis_core.field.QM31.ZERO
  let output1 ← Array.update output 0#usize q
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize group_index)
  let source1 ← lift (Std.Usize.wrapping_add i1 1#usize)
  let q1 ←
    if source1 >= start
    then
      do
      let i2 ← lift (Std.Usize.wrapping_add start N)
      if source1 < i2
      then
        let i3 ← lift (Std.Usize.wrapping_sub source1 start)
        Array.index_usize values i3
      else ok aspis_core.field.QM31.ZERO
    else ok aspis_core.field.QM31.ZERO
  let output2 ← Array.update output1 1#usize q1
  let i2 ← lift (Std.Usize.wrapping_mul 4#usize group_index)
  let source2 ← lift (Std.Usize.wrapping_add i2 2#usize)
  let q2 ←
    if source2 >= start
    then
      do
      let i3 ← lift (Std.Usize.wrapping_add start N)
      if source2 < i3
      then
        let i4 ← lift (Std.Usize.wrapping_sub source2 start)
        Array.index_usize values i4
      else ok aspis_core.field.QM31.ZERO
    else ok aspis_core.field.QM31.ZERO
  let output3 ← Array.update output2 2#usize q2
  let i3 ← lift (Std.Usize.wrapping_mul 4#usize group_index)
  let source3 ← lift (Std.Usize.wrapping_add i3 3#usize)
  let q3 ←
    if source3 >= start
    then
      do
      let i4 ← lift (Std.Usize.wrapping_add start N)
      if source3 < i4
      then
        let i5 ← lift (Std.Usize.wrapping_sub source3 start)
        Array.index_usize values i5
      else ok aspis_core.field.QM31.ZERO
    else ok aspis_core.field.QM31.ZERO
  let output4 ← Array.update output3 3#usize q3
  .ok output4
attribute [local irreducible] Array.index_usize Usize.wrapping_mul Usize.wrapping_add Usize.wrapping_sub
theorem preweighted_build_binding12 {N : Usize} (start : Usize) (values : Array aspis_core.field.QM31 N)
    (group_index : Usize) :
    preweighted_build_stores12 start values group_index =
      four_build12 (preweighted_window12 start values group_index) := by
  simpa only [preweighted_build_stores12,preweighted_window12,lift,bind_tc_ok,
    PV_B3P_Ordered227.bind_assoc,bind_branch12,bind_return12] using
    four_interleaved12 aspis_core.field.QM31.ZERO (preweighted_window12 start values group_index)
#print axioms preweighted_build_binding12
end PV_B3P_Binding12227
