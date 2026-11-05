import NHT_EmittedCommon
import NHQ_Tx2CommonModel
set_option autoImplicit false
noncomputable section
namespace NHT_Tx2CommonModel
open Aeneas Aeneas.Std Result VTop_Stages
/-- Install the actual emitted constants and transparent standard helpers. -/
def constants (ops : Ops) : Ops := {ops with
 op0 := @NHT_Constants.core.option.Option.ok_or
 op14 := NHT_Constants.compact.OFF_ROUND1
 op15 := NHT_Constants.compact.OFF_FOLDED_ROOT
 op16 := ok NHT_Constants.compact.SPLIT
 op20 := NHT_Constants.compact.OFF_OPENINGS
 op21 := NHT_Constants.compact.OFF_FINAL
 op22 := NHT_Constants.compact.OFF_ROUND0
 op23 := NHT_Constants.compact.OFF_INACTIVE
 unwrap32 := core.result.Result.unwrap core.fmt.DebugTryFromSliceError }

/-- Fresh transparent control body on canonical cohort carriers. No whole-driver
output hypothesis. Constants and standard helpers are exactly the emitted ones. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHT_EmittedCommon.tx2_common (constants ops) D pub proof checkpoint hash obs =
 verifier.candidate.tx2_common (constants ops) D pub proof checkpoint hash obs := by
 rfl

theorem retained_stages (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHT_EmittedCommon.tx2_common (constants ops) D pub proof checkpoint hash obs =
 NHQ_Tx2CommonModel.run (constants ops) D pub proof checkpoint hash obs :=
 (source ops D pub proof checkpoint hash obs).trans
  (NHQ_Tx2CommonModel.source (constants ops) D pub proof checkpoint hash obs)
#print axioms source
#print axioms retained_stages
end NHT_Tx2CommonModel
