import Aeneas
import AspisR1CanonicalQRaw.Funs
import SelectorArrayMapSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalDotFinish.Proof
open AspisV8R19.TraversalRuntime

private def fromFunctionItem : U32 → Result U64 :=
  fun x => .ok (core.convert.num.FromU64U32.from x)

private theorem mapState_fromFunctionItem (xs : List U32) :
    mapState (BuiltinFnMut U32 U64).call_mut xs fromFunctionItem =
      .ok (xs.map core.convert.num.FromU64U32.from, fromFunctionItem) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapState]
    have hx : (BuiltinFnMut U32 U64).call_mut fromFunctionItem x =
        .ok (core.convert.num.FromU64U32.from x, fromFunctionItem) := rfl
    rw [hx]
    simp only [bind_tc_ok]
    rw [ih]
    rfl

private theorem mapState_fromClosure (xs : List U32) :
    mapState
      canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapState]
    have hx :
        canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
          () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
      simp [canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
        core.convert.num.FromU64U32.from, lift]
    rw [hx]
    simp only [bind_tc_ok]
    rw [ih]
    rfl

theorem rawMap_functionItem_eq_captureFreeClosure (input : Array U32 4#usize) :
    Aeneas.Std.core.array.Array.map (BuiltinFnMut U32 U64) input
      fromFunctionItem =
    Aeneas.Std.core.array.Array.map
      canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      input () := by
  have hi := Aeneas.Std.core.array.Array.map_success
    (BuiltinFnMut U32 U64) input fromFunctionItem
    (input.val.map core.convert.num.FromU64U32.from) fromFunctionItem
    (mapState_fromFunctionItem input.val)
  have hc := Aeneas.Std.core.array.Array.map_success
    canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
    input () (input.val.map core.convert.num.FromU64U32.from) ()
    (mapState_fromClosure input.val)
  rw [hi, hc]

#print axioms mapState_fromFunctionItem
#print axioms mapState_fromClosure
#print axioms rawMap_functionItem_eq_captureFreeClosure
end AspisR1CanonicalDotFinish.Proof
