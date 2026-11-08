import NNV_ResultOkPort
import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishRounds
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open LIB_VCarriers

theorem returned (p : Prefix) (t : Transcript) (env : RSL.Env)
 (r : QM31 × Alpha × Transcript)
 (called : LIB_VLib.semanticRoundsValue (p,t) env = .ok r) :
 (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R
  (LIB_VCode.digest env) (prefixRaw p) t)).2 =
 .ok (.Ok (LIB_VScalarCarriers.toRaw r.1,alphaRaw r.2.1,r.2.2)) := by
 have hm := NNV_ResultOkPort.value (LIB_VRounds.model (p,t) env) .Terminal r called
 have exact_ := LIB_VRounds.model_exact (p,t) env
 rw [hm,bind_tc_ok] at exact_
 obtain ⟨raw,hr,image⟩ := NNV_ResultOkPort.mapped _ _ _ exact_.symm
 cases raw with
 | Err e => cases image
 | Ok out =>
  have same := Except.ok.inj image
  cases same
  exact hr
#print axioms returned
end AspisR1.NNV_FinishRounds
end
