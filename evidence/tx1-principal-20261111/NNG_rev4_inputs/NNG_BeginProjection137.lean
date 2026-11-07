import NNG_BeginSource137
import NNG_ChallengeProjection137
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BeginProjection137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
open NMP_ResultTransport (outer)

def decode (fallback : LIB_VCarriers.QM31)
    (reply : core.result.Result aspis_core.state_only_prefix.r0.Challenges r1_wire.Error × r1_wire.SemanticTranscript Unit) :
    Except LIB_VCarriers.WErr (LIB_VCarriers.Challenges × LIB_VCarriers.Transcript) :=
 match reply.1 with
 | .Err e=>.error (toT12 e)
 | .Ok c=>.ok (NNG_ChallengeProjection137.project fallback (toT3 c),toT10 reply.2)

theorem projected (fallback : LIB_VCarriers.QM31) (env : RSL.Env) (p : LIB_VCarriers.Prefix) (t : LIB_VCarriers.Transcript) :
    NNG_EmittedCallGraph.resultMap (decode fallback)
      (NMP_Install150.begin_ (NNG_PublicSource137.digest env) (fromT13 (LIB_VCarriers.prefixRaw p)) (fromT10 t)) =
      LIB_VBegin.model (p,t) env := by
  unfold NMP_Install150.begin_ LIB_VBegin.model
  rw [NNG_PublicSource137.digest_exact,fromT13_inverse,fromT10_inverse]
  split
  · rename_i c after h
    dsimp only at h
    conv_lhs=>rw [h]
    simp only [outer,NMP_Install150.fromReply,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,decode,fromT3_inverse,fromT10_inverse]
    have canonical := LIB_VChallenges.begin_canonical (LIB_VCode.digest env) p t after c h
    rw [NNG_ChallengeProjection137.lifted fallback c canonical]
  · rename_i e after h
    dsimp only at h
    conv_lhs=>rw [h]
    simp only [outer,NMP_Install150.fromReply,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,decode,fromT12_inverse]
  · rename_i e h
    dsimp only at h
    conv_lhs=>rw [h]
    rfl
  · rename_i h
    dsimp only at h
    conv_lhs=>rw [h]
    rfl
#print axioms projected
end AspisR1.NNG_BeginProjection137
