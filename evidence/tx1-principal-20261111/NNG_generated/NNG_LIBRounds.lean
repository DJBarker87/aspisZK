import NNG_LIBRoundProjection
import NNG_LIBDigest
import NNG_Model134
import LIB_VRounds
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBRounds
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays

def projectReply (fallback : Value) : core.result.Result (Q × Alpha × r1_wire.SemanticTranscript Unit) r1_wire.Error →
    Except LIB_VCarriers.WErr (Value × LIB_VCarriers.Alpha × LIB_VCarriers.Transcript)
 | .Ok (q,a,t) => .ok (project fallback q,projectArray fallback a,toT10 t)
 | .Err e => .error (toT13 e)

theorem projected (fallback : Value) (env : RSL.Env) (p : LIB_VCarriers.Prefix) (t : LIB_VCarriers.Transcript) :
    NNG_EmittedCallGraph.resultMap (projectReply fallback)
      (NNG_Model134.rounds (NNG_LIBDigest.digest env) (fromT12 (LIB_VCarriers.prefixRaw p)) (fromT10 t)) =
      LIB_VRounds.model (p,t) env := by
  unfold NNG_Model134.rounds NNG_Model134.model LIB_VRounds.model LIB_VRounds.code
  rw [NNG_LIBDigest.installed,fromT12_inverse,fromT10_inverse]
  split
  · rename_i after h
    rcases after with ⟨q,alpha,post⟩
    dsimp only at h
    conv_lhs => rw [h]
    simp only [NMP_ResultTransport.outer,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,projectReply,
      NNG_Model134.raiseReply,fromT10_inverse]
    have canonical := LIB_VRoundCanonical.rounds p (LIB_VCode.digest env) t (q,alpha,post) h
    rw [NNG_LIBRoundProjection.scalar fallback q canonical.1,
      NNG_LIBRoundProjection.array fallback alpha canonical.2]
  · rename_i e h
    dsimp only at h
    conv_lhs => rw [h]
    simp only [NMP_ResultTransport.outer,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,projectReply,fromT13_inverse]
  · rename_i e h
    dsimp only at h
    conv_lhs => rw [h]
    rfl
  · rename_i h
    dsimp only at h
    conv_lhs => rw [h]
    rfl
#print axioms projected
end AspisR1.NNG_LIBRounds
