import NNG_ConcreteGraph136
import NNG_LIBClaims
import NNG_LIBEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteClaims136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar

theorem occurrence (fallback : Value) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (borrow : p.source.val.length ≤ 57607) :
    RSL.Spec.map (NNG_LIBClaims.projectReply fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "claims" (fromT12 (LIB_VCarriers.prefixRaw p))
        (NNG_LIBClaims.call env (fromT12 (LIB_VCarriers.prefixRaw p)))) env = (LIB_VClaims.claims.run p) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VClaims.claims p borrow
    (NNG_LIBClaims.projectReply fallback) NNG_LIBEvents136.events "claims"
    (fromT12 (LIB_VCarriers.prefixRaw p)) _ env ⟨.ret (LIB_VClaims.eval p env),[]⟩
  · rw [NNG_LIBEvents136.silent env "claims" _ _ (by decide) (by decide) (by decide)]
    exact NNG_ConcreteGraph136.resultObs (NNG_LIBClaims.projectReply fallback) _ _ []
      (NNG_LIBClaims.projected fallback env p)
  · exact LIB_VClaims.law_exact p env
#print axioms occurrence
end AspisR1.NNG_ConcreteClaims136
