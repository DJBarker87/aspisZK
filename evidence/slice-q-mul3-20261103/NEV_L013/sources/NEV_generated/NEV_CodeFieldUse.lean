import NEV_CodeFieldBridge
import NBF_BasisDomain
set_option autoImplicit false
noncomputable section
namespace NEV_CodeFieldUse
open Aeneas Aeneas.Std Result
/-- The reached basis read supplies the constructor's canonical domain.  The
returned basis and selected value are the SAME ones used at the call site. -/
theorem basis_call (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32)
    (basis : Array U32 256#usize)
    (run : NBF_BasisDomain.source ops node=ok basis)
    (index : Usize) (bound : index.val<256) (word : U32)
    (read : Array.index_usize basis index=ok word) :
    (do let out ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 word
        ok (NEV_CodeFieldBridge.toStage out)) =
      (NBF_RowInstall.install ops).op10 word := by
  apply NEV_CodeFieldBridge.cohort
  have canonical := NBF_BasisDomain.read_canonical ops node basis run index bound word read
  change word.val<2147483647 at canonical
  exact canonical
#print axioms basis_call
end NEV_CodeFieldUse
end
