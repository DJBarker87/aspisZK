import NNG_ConcreteGraph136
import NNG_LIBRounds
import NNG_LIBEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteRounds136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar

theorem occurrence (fallback : Value) (env : RSL.Env) (p : LIB_VCarriers.Prefix) (t : LIB_VCarriers.Transcript)
    (borrow : p.source.val.length ≤ 57607) :
    RSL.Spec.map (NNG_LIBRounds.projectReply fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "rounds" (fromT12 (LIB_VCarriers.prefixRaw p),fromT10 t)
        (NNG_Model134.rounds (NNG_LIBDigest.digest env) (fromT12 (LIB_VCarriers.prefixRaw p)) (fromT10 t))) env =
      (LIB_VRounds.semanticRounds.run (p,t)) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VRounds.semanticRounds (p,t) borrow
    (NNG_LIBRounds.projectReply fallback) NNG_LIBEvents136.events "rounds"
    (fromT12 (LIB_VCarriers.prefixRaw p),fromT10 t) _ env
    (LIB_Carriers.resultObs id (LIB_VRounds.events (p,t) env) (LIB_VRounds.model (p,t) env))
  · rw [NNG_LIBEvents136.rounds]
    have values := NNG_ConcreteGraph136.resultObs (NNG_LIBRounds.projectReply fallback) _ _
      (LIB_VRounds.events (p,t) env) (NNG_LIBRounds.projected fallback env p t)
    simpa only [NNG_Model134.model,NNG_LIBDigest.installed,fromT12_inverse,fromT10_inverse,
      LIB_VRounds.events,LIB_VRounds.code] using values
  · exact LIB_VRounds.law_exact (p,t) env
#print axioms occurrence
end AspisR1.NNG_ConcreteRounds136
