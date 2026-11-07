import NNG_ConcreteGraph136
import NNG_LIBTerminal
import NNG_LIBEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteTerminal136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays

theorem occurrence (fallback : Value) (env : RSL.Env) (a : LIB_VTerminal.Args)
    (domain : LIB_VTerminal.Domain a) :
    RSL.Spec.map (NNG_LIBTerminal.projectReply fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "terminal"
        (fromT9 a.1,lowerClaims a.2.1,lowerArray a.2.2.1,lowerChallenges a.2.2.2)
        (NNG_ModelTerminal.call (fromT9 a.1) (lowerClaims a.2.1) (lowerArray a.2.2.1) (lowerChallenges a.2.2.2))) env =
      (LIB_VTerminal.terminalQm31.run a) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VTerminal.terminalQm31 a domain
    (NNG_LIBTerminal.projectReply fallback) NNG_LIBEvents136.events "terminal"
    (fromT9 a.1,lowerClaims a.2.1,lowerArray a.2.2.1,lowerChallenges a.2.2.2) _ env
    (LIB_Carriers.resultObs id [] (LIB_VTerminal.model a))
  · rw [NNG_LIBEvents136.silent env "terminal" _ _ (by decide) (by decide) (by decide)]
    exact NNG_ConcreteGraph136.resultObs (NNG_LIBTerminal.projectReply fallback) _ _ []
      (NNG_LIBTerminal.projected fallback a domain)
  · exact LIB_VTerminal.law_exact a env
#print axioms occurrence
end AspisR1.NNG_ConcreteTerminal136
