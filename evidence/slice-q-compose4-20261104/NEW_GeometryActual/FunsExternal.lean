import NEW_GeometryActual.Types
import OraclePortStdBuilder
import Port4C_GeometryStd
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

/-- Reuse the existing state-threading std array interpretation verbatim. -/
def core.array.from_fn {T F : Type} (n : Usize) (f : core.ops.function.FnMut F Usize T) :
    F → Result (Array T n) := AspisR1.OraclePortStdBuilder.fromFn n f

def core.iter.traits.iterator.Iterator.any.default {Self F Item : Type}
    (it : core.iter.traits.iterator.Iterator Self Item)
    (f : core.ops.function.FnMut F Item Bool) : Self → F → Result (Bool × Self) :=
  AspisR1.Port3_BatchStd.anyDefault it f

def core.iter.traits.iterator.Iterator.map.default {Self B F Item : Type}
    (it : core.iter.traits.iterator.Iterator Self Item)
    (f : core.ops.function.FnMut F Item B) :
    Self → F → Result (core.iter.adapters.map.Map Self F) :=
  AspisR1.OraclePortStdBuilder.iterMap it f

def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next {B I F Item : Type}
    (it : core.iter.traits.iterator.Iterator I Item)
    (f : core.ops.function.FnMut F Item B) :
    core.iter.adapters.map.Map I F → Result (Option B × core.iter.adapters.map.Map I F) :=
  AspisR1.OraclePortStdBuilder.mapNext it f

def core.result.Result.map_err {T E F O : Type} (f : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F) :=
  AspisR1.Port4C_GeometryStd.mapError f

def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any {T F : Type}
    (f : core.ops.function.FnMut F T Bool) :
    core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T) :=
  AspisR1.Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T) f

def alloc.vec.Vec.is_empty {T : Type} (_A : Type) (v : alloc.vec.Vec T) : Result Bool :=
  ok v.val.isEmpty

/-- Frozen r0/mod.rs::FIBRE_COUNT = 1 << 18. Source equality is checked separately. -/
def NEW_GeometryActual.aspis_core.r0.FIBRE_COUNT : Result Usize := ok 262144#usize
