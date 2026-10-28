import NBY_Audit
import Port4B_NativeReject

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_ErrorObstruction
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- A faithful local Rust padding return cannot equal the retained emitted
return, even on the SAME arbitrary scratch carrier. This imports the known
counterexample; no new extraction or alternate model is introduced. -/
theorem exact_error_obstruction
    (idx : Indices) (val : Values)
    (native : Result (core.result.Result Unit verifier.Error × Indices × Values))
    (nativeStep : native = ok (.Err verifier.Error.Parse,idx,val)) :
    native ≠ (do
      let (i,v,p) ← Port4B_Rejection.emittedPadding idx val
      Port4B_Rejection.emittedReturn i v p) := by
  obtain ⟨_,rust,unequal⟩ := Port4B_Rejection.padding_result_differs idx val
  rw [nativeStep,←rust]
  exact Ne.symm unequal

/-- The mismatch persists after ANY already-issued chronological prefix.
Retaining the prefix does not make the two exact return values equal. -/
theorem exact_error_and_prefix_obstruction
    (idx : Indices) (val : Values) {Entry : Type} (before : List Entry)
    (native : Result (core.result.Result Unit verifier.Error × Indices × Values))
    (nativeStep : native = ok (.Err verifier.Error.Parse,idx,val)) :
    (before,native) ≠ (before,(do
      let (i,v,p) ← Port4B_Rejection.emittedPadding idx val
      Port4B_Rejection.emittedReturn i v p)) := by
  intro same
  exact exact_error_obstruction idx val native nativeStep (congrArg Prod.snd same)

#print axioms exact_error_obstruction
#print axioms exact_error_and_prefix_obstruction
end AspisR1.NCE_ErrorObstruction
end
