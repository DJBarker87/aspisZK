import XSe_OldHighZero
import XSe_EnumeratedDriver
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSe_ValidatorBody
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)
def body (row : U8) (iter : Iter) :
 Result (ControlFlow Iter (core.result.Result Unit XSe_ValidatorStage.OldError)) := do
 let (item,after) ← core.iter.adapters.enumerate.IteratorEnumerate.next
  (core.iter.traits.iterator.IteratorChunksExact U8) iter
 match item with
 | none => ok (.done (.Ok ()))
 | some (i,bytes) => do
   let status ← XSe_ValidatorStage.old row i bytes
   match status with
   | .Err e => ok (.done (.Err e))
   | .Ok _ => ok (.cont after)
/-- Preserve the full actual iterator body, including its current error index. -/
theorem source (row : U8) (iter : Iter) :
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body row iter=body row iter := by
 unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body body
 congr 1
 funext pair
 rcases pair with ⟨item,after⟩
 dsimp! only
 cases item with
 | none => rfl
 | some pair =>
  rcases pair with ⟨i,bytes⟩
  dsimp! only
  unfold XSe_ValidatorStage.old
  simp only [bind_assoc_eq]
  congr 1
  funext value
  cases value with
  | none => rfl
  | some w =>
    simp only [AspisR1PrefixAggregateParser.core.option.Option.ok_or,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTry.branch,
     AspisR1PrefixAggregateParser.field.wide_exact.WideExact.impl.c1]
    rw [XSe_OldHighZero.source]
    simp only [bind_tc_ok]
    cases hz : XSe_OldHighZero.zero w.c1 <;> simp_all [XSe_OldHighZero.zero]
#print axioms source
end XSe_ValidatorBody
