import Port3_NativeBatchCalls

/-! Concrete pure std/copy/constant leaves for the native batch parent.
Packed-key, leaf, node-count and verifier P6 children remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_BatchStd
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody

def anyBody {Self F Item : Type} (iter : core.iter.traits.iterator.Iterator Self Item)
    (pred : core.ops.function.FnMut F Item Bool) (state : Self × F) :
    Result (ControlFlow (Self × F) (Bool × Self)) := do
  let (next,s) ← iter.next state.1
  match next with
  | none => ok (.done (false,s))
  | some value =>
    let (stop,f) ← pred.call_mut state.2 value
    if stop then ok (.done (true,s)) else ok (.cont (s,f))

def anyDefault {Self F Item : Type} (iter : core.iter.traits.iterator.Iterator Self Item)
    (pred : core.ops.function.FnMut F Item Bool) (s : Self) (f : F) : Result (Bool × Self) :=
  loop (anyBody iter pred) (s,f)

def okOr {T E : Type} (value : Option T) (error : E) : Result (core.result.Result T E) :=
  match value with | some x => ok (.Ok x) | none => ok (.Err error)

def unwrap8 (value : core.result.Result (Array U8 8#usize) core.array.TryFromSliceError) :
    Result (Array U8 8#usize) :=
  match value with | .Ok x => ok x | .Err _ => fail .panic

def sameLeaf (values : Array (Array U8 32#usize) 16#usize) (index : Usize) (leaf : Array U8 32#usize) :
    Result Bool := do
  let value ← Array.index_usize values index
  ok (decide (value=leaf))

def sameIndex (values : Array U32 16#usize) (index : Usize) (expected : U32) : Result Bool := do
  let value ← Array.index_usize values index
  ok (decide (value=expected))

def install (base : Ops) : Ops :=
  {base with op0:=anyDefault,op1:=okOr,op7:=sameLeaf,op8:=sameIndex,
    op9:=Array.index_usize,
    op12:=ok (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]),
    op13:=ok 10#usize,unwrap8:=unwrap8}

theorem same_leaf_read (values : Array (Array U8 32#usize) 16#usize) (index : Usize) (leaf : Array U8 32#usize)
    (value : Array U8 32#usize) (read : Array.index_usize values index=ok value) :
    sameLeaf values index leaf=ok (decide (value=leaf)) := by
  simp only [sameLeaf,read,bind_tc_ok]

theorem same_index_read (values : Array U32 16#usize) (index : Usize) (expected value : U32)
    (read : Array.index_usize values index=ok value) :
    sameIndex values index expected=ok (decide (value=expected)) := by
  simp only [sameIndex,read,bind_tc_ok]

#print axioms anyDefault
#print axioms install
#print axioms same_leaf_read
#print axioms same_index_read
end AspisR1.Port3_BatchStd
end
