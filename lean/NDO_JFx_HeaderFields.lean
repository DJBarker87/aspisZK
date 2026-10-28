import NDO_JFx_NativeHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_HeaderFields
open Aeneas Aeneas.Std Result
open JFx_NativeBytes

theorem fields : proof.val.length = 57607 ∧
    proof.val.take 8 = Op3I_Source.compact.MAGIC.val ∧
    proof.val[8]? = some 2#u8 ∧
    (proof.val.drop 9).take 7 = List.replicate 7 0#u8 := by
  refine ⟨proofBytes_length,?_,?_,?_⟩
  · have h := congrArg (List.take 8) JFx_NativeHeader.first_sixteen
    simpa only [List.take_take,show min 8 16=8 by decide,
      List.take_succ_cons,List.take_zero,Op3I_Source.compact.MAGIC,Array.make] using h
  · have h := congrArg (fun xs : List U8 => xs[8]?) JFx_NativeHeader.first_sixteen
    simpa only [List.getElem?_take_of_lt (by decide : 8<16),
      List.getElem?_cons_succ,List.getElem?_cons_zero] using h
  · rw [List.take_drop,show 9+7=16 by decide,JFx_NativeHeader.first_sixteen]
    rfl

/-- Shape acceptance of the ACTUAL retained native proof bytes. This is only
the op3 gate; it does not assert complete native or cryptographic acceptance. -/
theorem shape_accepted : Op3I_Install.sourceBody proof = ok (.Ok .S2) :=
  Op3I_Nonvacuity.source_of_fields proof fields.1 fields.2.1 fields.2.2.1 fields.2.2.2

#print axioms fields
#print axioms shape_accepted
end AspisR1.JFx_HeaderFields
end
