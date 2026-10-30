import PV_B3P_NativePreweighted15227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
def host_terminal.add_preweighted_loop0_loop0.body
  {N : Std.Usize} (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
  (group : Std.Usize) (output : Array aspis_core.field.QM31 4#usize)
  (slot : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 4#usize) × Std.Usize)
    (Array aspis_core.field.QM31 4#usize))
  := do
  if slot < 4#usize
  then
    let i ← lift (Std.Usize.wrapping_mul 4#usize group)
    let source ← lift (Std.Usize.wrapping_add i slot)
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
    let output1 ← Array.update output slot q
    let slot1 ← lift (Std.Usize.wrapping_add slot 1#usize)
    ok (cont (output1, slot1))
  else ok (done output)

def host_terminal.add_preweighted_loop0_loop0
  {N : Std.Usize} (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
  (group : Std.Usize) (output : Array aspis_core.field.QM31 4#usize)
  (slot : Std.Usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  loop
    (fun (output1, slot1) => host_terminal.add_preweighted_loop0_loop0.body
      start values group output1 slot1)
    (output, slot)

def host_terminal.add_preweighted_loop0.body
  {N : Std.Usize} (start : Std.Usize) (values : Array aspis_core.field.QM31 N)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 24#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Array
    aspis_core.field.QM31 24#usize)) (Array aspis_core.field.QM31 24#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done packed)
  | some group =>
    let output := Array.repeat 4#usize aspis_core.field.QM31.ZERO
    let lanes ←
      host_terminal.add_preweighted_loop0_loop0 start values group output
        0#usize
    let q ← Array.index_usize packed group
    let s ← lift (Array.to_slice lanes)
    let q1 ← host_terminal_field.qm31_pack_base4 s
    let q2 ← aspis_core.field.QM31.add q q1
    let packed1 ← Array.update packed group q2
    ok (cont (iter1, packed1))

def host_terminal.add_preweighted_loop0
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array aspis_core.field.QM31 24#usize) (start : Std.Usize)
  (values : Array aspis_core.field.QM31 N) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  loop
    (fun (iter1, packed1) => host_terminal.add_preweighted_loop0.body start
      values iter1 packed1)
    (iter, packed)

def host_terminal.add_preweighted
  {N : Std.Usize} (packed : Array aspis_core.field.QM31 24#usize)
  (start : Std.Usize) (values : Array aspis_core.field.QM31 N) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let first ← start / 4#usize
  let i ← lift (Std.Usize.wrapping_add start N)
  let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
  let last ← i1 / 4#usize
  let iter ← core.ops.range.RangeInclusive.new first last
  host_terminal.add_preweighted_loop0 iter packed start values
end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding12227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.add host_terminal_field.qm31_pack_base4

theorem preweighted_inner_body17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (group : Usize)
    (output : Array aspis_core.field.QM31 4#usize) (slot : Usize) :
    host_terminal.add_preweighted_loop0_loop0.body start values group output slot =
      usize_body (window_store12 (preweighted_window12 start values group)) 4#usize (output,slot) := by
  by_cases h : slot < 4#usize <;>
    simp only [host_terminal.add_preweighted_loop0_loop0.body,usize_body,
      window_store12,preweighted_window12,h,if_true,if_false,PV_B3P_Ordered227.bind_assoc,
      lift,bind_tc_ok]

theorem preweighted_inner_loop17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (group : Usize)
    (output : Array aspis_core.field.QM31 4#usize) (slot : Usize) :
    host_terminal.add_preweighted_loop0_loop0 start values group output slot =
      loop (usize_body (window_store12 (preweighted_window12 start values group)) 4#usize) (output,slot) := by
  unfold host_terminal.add_preweighted_loop0_loop0
  have same : (fun (state : Array aspis_core.field.QM31 4#usize × Usize) =>
      host_terminal.add_preweighted_loop0_loop0.body start values group state.1 state.2) =
      usize_body (window_store12 (preweighted_window12 start values group)) 4#usize := by
    funext state
    exact preweighted_inner_body17 start values group state.1 state.2
  rw [same]

theorem preweighted_four17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (group : Usize) :
    host_terminal.add_preweighted_loop0_loop0 start values group
      (Array.repeat 4#usize aspis_core.field.QM31.ZERO) 0#usize =
      source_four_loop12 aspis_core.field.QM31.ZERO (preweighted_window12 start values group) := by
  exact preweighted_inner_loop17 start values group _ _
#print axioms preweighted_inner_body17
#print axioms preweighted_inner_loop17
#print axioms preweighted_four17
end PV_B3P_Direct17227
