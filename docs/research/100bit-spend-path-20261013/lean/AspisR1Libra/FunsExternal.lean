import AspisR1Libra.Types
import CuSavingsArrayBuilder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Libra
class Shared where
  add : field.wide_exact.WideExact → field.wide_exact.WideExact → Result field.wide_exact.WideExact
  mul : field.wide_exact.WideExact → field.wide_exact.WideExact → Result field.wide_exact.WideExact
  mulK : field.wide_exact.WideExact → field.QM31 → Result field.wide_exact.WideExact
  mulM : field.wide_exact.WideExact → field.M31 → Result field.wide_exact.WideExact
  kMul : field.QM31 → field.QM31 → Result field.QM31
  kSquare : field.QM31 → Result field.QM31
abbrev field.wide_exact.WideExact.add [Shared] := Shared.add
abbrev field.wide_exact.WideExact.mul [Shared] := Shared.mul
abbrev field.wide_exact.WideExact.mul_qm31 [Shared] := Shared.mulK
abbrev field.wide_exact.WideExact.mul_m31 [Shared] := Shared.mulM
abbrev field.QM31.mul [Shared] := Shared.kMul
abbrev field.QM31.square [Shared] := Shared.kSquare
def core.iter.traits.iterator.Iterator.fold.default {Self B F Item : Type}
    (iter : core.iter.traits.iterator.Iterator Self Item)
    (callback : core.ops.function.FnMut F (B × Item) B)
    (initial : Self) (value : B) (closure : F) : Result B :=
  loop (fun (state,acc,c) => do
    let (entry,state1) ← iter.next state
    match entry with
    | none => .ok (.done acc)
    | some item =>
      let (acc1,c1) ← callback.call_mut c (acc,item)
      .ok (.cont (state1,acc1,c1))) (initial,value,closure)
abbrev core.array.from_fn := @AspisR1.CuSavingsArrayBuilder.build
def core.array.from_fn_mut {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) : Result (Array T N × F) := do
  let (xs,finalState) ← AspisR1.CuSavingsArrayBuilder.cells inst N.val 0#usize state
  .ok (⟨xs.val,xs.property⟩,finalState)
#print axioms Shared
end AspisR1Libra
