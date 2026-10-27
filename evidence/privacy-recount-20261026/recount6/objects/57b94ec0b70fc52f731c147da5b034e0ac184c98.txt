import R1Z.ProverRwSuccessWideSource
import R1Z.ProverRwSuccessArrayFromFn
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessCoefficientsSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev core.array.from_fn := @ProverRwSuccessArrayFromFn.fromFn
abbrev transport.Variant := ProverRwFull.transport.Variant
abbrev transport.Variant.coefficients.closure (T : Type) := Array T 1024#usize × transport.Variant
def transport.TAU : Array Std.Usize 5#usize :=
  Array.make 5#usize [ 3#usize, 4#usize, 2#usize, 0#usize, 1#usize ]

def transport.Variant.row_loop.body
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize)
    Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some d =>
    let i ← 2#usize * d
    let i1 ← j >>> i
    let i2 ← lift (i1 &&& 3#usize)
    let i3 ← Array.index_usize transport.TAU d
    let i4 ← 2#usize * i3
    let i5 ← i2 <<< i4
    let out1 ← lift (out ||| i5)
    ok (cont (iter1, out1))

def transport.Variant.row_loop
  (iter : core.ops.range.Range Std.Usize) (j : Std.Usize) (out : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, out1) => transport.Variant.row_loop.body j iter1 out1)
    (iter, out)

def transport.Variant.row
  (self : transport.Variant) (j : Std.Usize) : Result Std.Usize := do
  transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j
      0#usize

def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : transport.Variant.coefficients.closure T) (tupled_args : Std.Usize) :
  Result (T × (transport.Variant.coefficients.closure T))
  := do
  let (a, v) := c
  let i ← transport.Variant.row v tupled_args
  let t ← Array.index_usize a i
  ok (t, c)

def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT.call_once
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : transport.Variant.coefficients.closure T) (i : Std.Usize) :
  Result T
  := do
  let (t, _) ←
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      coremarkerCopyInst c i
  ok t

def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnOnce (transport.Variant.coefficients.closure T) Std.Usize
  T := {
  call_once :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT.call_once
    coremarkerCopyInst
}

def
  transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnMut (transport.Variant.coefficients.closure T) Std.Usize
  T := {
  FnOnceInst :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT
    coremarkerCopyInst
  call_mut :=
    transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
    coremarkerCopyInst
}

def transport.Variant.coefficients
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (self : transport.Variant) (rows : Array T 1024#usize) :
  Result (Array T 1024#usize)
  := do
  core.array.from_fn 1024#usize
    (transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
    coremarkerCopyInst) (rows, self)
end R1Z.ProverRwSuccessCoefficientsSource
