import NBN_EncoderResult
import NBK_DeployedCallbackSelection
set_option autoImplicit false
noncomputable section
namespace NBN_InstalledEncoder
open Aeneas Aeneas.Std Result
open AspisR1
open AspisS6OuterNativeOps AspisS6CurrentAdapterCarrier

theorem source {F E : Type} (c : DrvC_Installation.Configuration F E)
    (s : AspisS6CurrentCodecInstallation.Statement) :
    (DrvC_Installation.sdk c).op22 s =
      resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1)
        (NBN_EncoderResult.result (toPoolV1PairForestTerminalStatementV1 s)) := by
  change AspisS6CurrentCodecInstallation.encode s = _
  unfold AspisS6CurrentCodecInstallation.encode
  rw [NBN_EncoderResult.source]

#print axioms source
end NBN_InstalledEncoder
