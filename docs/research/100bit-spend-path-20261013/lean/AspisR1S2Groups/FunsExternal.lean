import AspisR1S2Groups.Types
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S2Groups
/- Shared computations only, with no propositional/algebraic fields.
The source raw(0,_) branch never invokes the unrelated fold/QM operations. -/
class Shared where
  add : field.wide_exact.WideExact → field.wide_exact.WideExact → Result field.wide_exact.WideExact
  mul : field.wide_exact.WideExact → field.wide_exact.WideExact → Result field.wide_exact.WideExact
  decode : Slice U8 → Result (Option field.wide_exact.WideExact)
  subK : field.QM31 → field.QM31 → Result field.QM31
  mulK : field.QM31 → field.QM31 → Result field.QM31
  powK : field.QM31 → U64 → Result field.QM31
  debugFmt : r0.Error → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  dRows : Result (Array U16 1024#usize)
  iterFold : {Self B F Item : Type} → core.iter.traits.iterator.Iterator Self Item →
    core.ops.function.FnMut F (B × Item) B → Self → B → F → Result B
  sliceFold : {T B F : Type} → core.ops.function.FnMut F (B × T) B →
    core.slice.iter.Iter T → B → F → Result B
abbrev field.wide_exact.WideExact.add [Shared] := Shared.add
abbrev field.wide_exact.WideExact.mul [Shared] := Shared.mul
abbrev field.wide_exact.WideExact.from_le_bytes [Shared] := Shared.decode
abbrev field.QM31.sub [Shared] := Shared.subK
abbrev field.QM31.mul [Shared] := Shared.mulK
abbrev field.QM31.pow [Shared] := Shared.powK
abbrev r0.Error.Insts.CoreFmtDebug.fmt [Shared] := Shared.debugFmt
abbrev r0.transport.COEFFICIENT_TO_ROW [Shared] := Shared.dRows
abbrev core.iter.traits.iterator.Iterator.fold.default [Shared] := @Shared.iterFold _
abbrev core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold [Shared] := @Shared.sliceFold _
#print axioms Shared
end AspisR1S2Groups
