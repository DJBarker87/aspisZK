import PSem_RowStep
set_option autoImplicit false
namespace AspisR1.PSem_RowControl
open Aeneas Aeneas.Std Result PSem_Control
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame
open AspisS1ValuesOwnedInstallation

/-- A reached source row cannot terminate the successful whole loop. Codec
errors terminate with Err; successful rows continue at their actual next state. -/
theorem cannot_finish (input out updated : Slice U8)
    (iter nextIter : core.ops.range.Range U8) (row tag : U8) (size src dst : Usize)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter=ok (some row,nextIter))
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (call : compact.expand_semantic_loop.body nativeValues input iter out src dst=
      ok (.done (.Ok (),updated))) : False := by
  unfold compact.expand_semantic_loop.body at call
  obtain ⟨next,it,hit,call⟩ := pair_success _ _ _ call
  have nextEq := Result.ok.inj (hit.symm.trans advance)
  have oEq : next=some row := congrArg Prod.fst nextEq
  have itEq : it=nextIter := congrArg Prod.snd nextEq
  subst next
  subst it
  obtain ⟨actualShape,hshape,call⟩ := bind_success _ _ _ call
  have shapeEq : actualShape=some (tag,size) := Result.ok.inj (hshape.symm.trans shape)
  subst actualShape
  simp (config := {zeta := true}) only [core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
  obtain ⟨_,_,call⟩ := bind_success _ _ _ call
  obtain ⟨_,_,_,call⟩ := pair_success _ _ _ call
  obtain ⟨_,_,call⟩ := bind_success _ _ _ call
  obtain ⟨_,_,call⟩ := bind_success _ _ _ call
  obtain ⟨_,_,call⟩ := bind_success _ _ _ call
  obtain ⟨flag,_,call⟩ := bind_success _ _ _ call
  cases flag with
  | false =>
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,_,call⟩ := pair_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    cases call
  | true =>
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,call⟩ := bind_success _ _ _ call
    obtain ⟨_,_,_,call⟩ := pair_success _ _ _ call
    obtain ⟨status,_,_,call⟩ := pair_success _ _ _ call
    cases status with
    | Err error =>
      change ok (ControlFlow.done (.Err error,_) : ControlFlow State Exit)=
        ok (ControlFlow.done (.Ok (),updated)) at call
      cases call
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
      obtain ⟨_,_,call⟩ := bind_success _ _ _ call
      cases call

#print axioms cannot_finish
end AspisR1.PSem_RowControl
