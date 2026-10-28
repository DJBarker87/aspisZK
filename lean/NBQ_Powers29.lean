import LPi_PowersSource
import LPm_PowersBridge
set_option autoImplicit false
namespace NBQ_Powers29
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues LPi_PowersPrefix
/-- Same gamma and same29-element returned carrier; all canonical intermediates
follow from the source induction and Lean-discharged multiplication. -/
theorem source (gamma : NE) (hg : canonE gamma) :
    ∃ out, FIo_Native.weights.powers 29#usize gamma=ok out ∧ Holds out (ew gamma) 29 :=
  LPi_PowersSource.source 29#usize gamma hg
/-- Arbitrary native step trace identifies the entire29-element carrier with
the emitted Result; no output equation or per-output canonicality is assumed. -/
theorem native_result (gamma : NE) (hg : canonE gamma) (out : Array NE 29#usize)
    (tr : LPm_PowersBridge.Trace gamma 29
      FIo_Native.aspis_core.field.wide_exact.WideExact.ONE out.val) :
    FIo_Native.weights.powers 29#usize gamma=ok out := by
  obtain ⟨model,call,holds⟩ := source gamma hg
  have native := LPm_PowersBridge.trace_values tr 0 rfl
  have same : model=out := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact model.property.trans out.property.symm
    · intro i hi hj
      have bound : i<29 := by have hlen : model.val.length=29 := model.property;omega
      obtain ⟨z,hz,_,vz⟩ := holds i bound
      obtain ⟨w,hw,_,vw⟩ := native i bound
      rw [List.getElem?_eq_getElem hi] at hz
      rw [List.getElem?_eq_getElem hj] at hw
      rw [Option.some.inj hz,Option.some.inj hw]
      exact LPm_PowersBridge.values_injective z w (vz.trans (by simpa using vw.symm))
  rw [same] at call;exact call
#print axioms source
#print axioms native_result
end NBQ_Powers29
