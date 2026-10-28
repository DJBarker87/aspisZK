import LPt_LPn_ExpandTrace
import JFw_Values
set_option autoImplicit false
namespace AspisR1.NBR_ValuesPort
open Aeneas Aeneas.Std Result

/-- The suspended native values leaf and the semantic expansion's owned
reference return the SAME complete buffer on every reached compact row.
Alignment/shape are metadata derived by K002/K005, not canonicality. -/
theorem construct (input initial : Slice U8)
    (bound : input.val.length≤1856) (aligned : input.val.length%16=0)
    (shape : initial.val.length=2*input.val.length) :
    ∃ returned : Slice U8,
      LPt_LPn.Expand.NativeTrace input.val initial.val (input.val.length/16) returned.val ∧
      LPt_External.compact.expand_values input initial=ok (.Ok (),returned) ∧
      AspisS1ValuesOwnedInstallation.expandValues input initial=ok (.Ok (),returned) := by
  obtain ⟨after,trace⟩ := LPt_LPn.Expand.total input.val initial.val (input.val.length/16)
  have inherited := LPt_LPn.Expand.to_inherited _ _ _ _ trace
  have length := LPt_LPl.Expand.length _ _ _ _ inherited
  let returned : Slice U8 := ⟨after,by rw [length];exact initial.property⟩
  have native := LPt_LPn.Expand.native_result input initial returned bound aligned shape trace
  obtain ⟨output,call,size,bytes⟩ := AspisS1ValuesOwnedExact.installed_exact input initial
    aligned shape (by scalar_tac)
  have sameBytes : output.val=after := by
    apply List.ext_getElem
    · exact size.trans length.symm
    · intro j hj hk
      have one : output.val[j]?.getD 0#u8=LPt_LPl_A.Expand.byte input.val j := by
        rw [bytes j hj]
        unfold LPt_LPl_A.Expand.byte
        by_cases low : j%32<16 <;> simp only [low,↓reduceIte,Option.getD_some]
      have two := LPt_LPl.Expand.invariant _ _ _ _ inherited j (by omega)
      rw [if_pos (by omega)] at two
      simp only [List.getElem?_eq_getElem hj,Option.getD_some] at one
      simp only [List.getElem?_eq_getElem hk,Option.getD_some] at two
      exact one.trans two.symm
  have same : output=returned := Subtype.ext sameBytes
  exact ⟨returned,trace,native,by simpa only [same] using call⟩

/-- Associate the already-returned native leaf buffer with the precise
semantic-expansion callee slot. No independently chosen successful output. -/
theorem returned (input initial output : Slice U8)
    (bound : input.val.length≤1856) (aligned : input.val.length%16=0)
    (shape : initial.val.length=2*input.val.length)
    (call : LPt_External.compact.expand_values input initial=ok (.Ok (),output)) :
    AspisS1ValuesOwnedInstallation.expandValues input initial=ok (.Ok (),output) := by
  obtain ⟨same,trace,native,semantic⟩ := construct input initial bound aligned shape
  have eqn : same=output := (Prod.mk.inj (Result.ok.inj (native.symm.trans call))).2
  simpa only [eqn] using semantic

#print axioms construct
#print axioms returned
end AspisR1.NBR_ValuesPort
