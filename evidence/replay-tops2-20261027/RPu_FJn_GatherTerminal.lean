import RPu_FJn_GatherProjection
import RPu_FJn_TerminalClaimsCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_GatherTerminal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
/-- Transport the complete terminal model to the SAME original width29 rows. -/
theorem value {L : Type} [Field L] (f : K →+* L)
    (c : FIr_GatherCallback.Claims) (out : Array field.QM31 84#usize)
    (run : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      FIr_GatherCanonical.callback field.QM31.ZERO c=ok out)
    (p : R0P.Public L) (lambda chi theta mu : L) (zc point : Fin 10 → L)
    {F : Subfield L} (B : R0P.PackBasis F) :
    R0P.SemSource.terminalValue p lambda chi theta mu zc B
      (fun j l=>f (FJn_ClaimsModel.claims out j l)) point=
    R0P.SemSource.terminalValue p lambda chi theta mu zc B
      (fun j l=>f (FJn_GatherProjection.claims c j l)) point := by
  apply FJn_TerminalClaimsCongr.value
  · intro j i
    apply congrArg f
    exact FJn_GatherProjection.value c out run j (Fin.castLE (by omega) i) (by change i.val<28;omega)
  · apply congrArg f
    exact FJn_GatherProjection.value c out run 0 26 (by decide)
#print axioms value
end AspisR1.FJn_GatherTerminal
end
