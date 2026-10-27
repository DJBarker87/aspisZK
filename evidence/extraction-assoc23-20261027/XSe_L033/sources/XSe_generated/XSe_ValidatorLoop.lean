import XSe_ValidatorIter
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSe_ValidatorLoop
open XSe_ValidatorBody XSe_ValidatorIter
/-- The emitted loop's entire first-stop execution, on arbitrary chunks and
remainder, associates to the one generic enumerated fold. -/
theorem source (row : U8) (chunks : List (Slice U8)) (remainder : Slice U8) (i : Usize) :
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop ⟨⟨chunks,remainder⟩,i⟩ row=
 XRo_Join_Carriers.mapR XSe_EnumeratedDriver.finish
  (XSe_ListDriver.fold (XSe_EnumeratedDriver.step next (stage row)) chunks (.Ok i)) := by
 induction chunks generalizing i with
 | nil =>
   unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop
   rw [loop,XSe_ValidatorBody.source]
   rfl
 | cons chunk rest ih =>
   unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop
   rw [loop,XSe_ValidatorBody.source]
   unfold body core.iter.adapters.enumerate.IteratorEnumerate.next
   simp only [core.slice.iter.IteratorChunksExact.next,bind_tc_ok]
   simp only [bind_assoc_eq]
   simp only [XSe_ListDriver.fold,XSe_EnumeratedDriver.step,next,stage,
    XRo_Join_Carriers.mapR_bind]
   cases hn : (i+1#usize : Result Usize) with
   | fail e => rfl
   | div => rfl
   | ok i' =>
     simp only [hn,bind_tc_ok]
     dsimp! only
     cases hs : XSe_ValidatorStage.old row i chunk with
     | fail e => rfl
     | div => rfl
     | ok status =>
       simp only [hs,bind_tc_ok]
       cases status with
       | Err e => cases rest <;> rfl
       | Ok u => exact ih i'
#print axioms source
end XSe_ValidatorLoop
