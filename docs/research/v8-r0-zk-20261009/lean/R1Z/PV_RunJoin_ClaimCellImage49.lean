import R1Z.PV_RunJoin_ClaimColumn49
import R1Z.PV_RunJoin_WideArithmetic44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimCellImage49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem source (z : Old.Q) :
    PV_RunJoin_WideImage43.source (z,zero)=fromW (ProverCommitNativeOps47.embedded z) := rfl

theorem value (z : Old.Q) :
    ProverCommitWideOps48.value (z,zero)=ProverCommitValueRange47.embed (decode z) := by
  rw [ProverCommitWideOps48.value,zero_decode,ProverCommitValueRange47.embed_coordinates]

theorem complete (z : Old.Q) (hz : Canonical z) :
    (PV_RunJoin_FlatBytes35.wire (fromW (ProverCommitNativeOps47.embedded z))).val.map PV_RunJoin_WideImage43.byte=
      List.ofFn (ProverCommitValueRange47.bytes (ProverCommitValueRange47.embed (decode z))) := by
  rw [←source,PV_RunJoin_WideImage43.image (z,zero) ⟨hz,zero_canonical⟩,
    ProverCommitWideBytes48.source_image,value]
#print axioms source
#print axioms value
#print axioms complete
end R1Z.PV_RunJoin_ClaimCellImage49
