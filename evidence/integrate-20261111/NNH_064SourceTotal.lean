import NNH_064PrefixCoverage
import LIBB_ObservationModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064SourceTotal
open Aeneas Aeneas.Std VTop_Stages
/-- Total source computation with the same Env digest and reservation binder.
This definition is not a choice from the weak Spec. Native occurrence adequacy
is a separate obligation; this module does not claim it. -/
def run (env : RSL.Env) (pub proof ck : Slice U8) :
 RSL.Obs (Except verifier.Error Unit) :=
 LIBB_Tx2EnvTrace.observation env pub proof ck

/-- The total source computation has the canonical library observation law.
This direction is source membership, not native-to-source adequacy. -/
theorem canonical (env : RSL.Env) (pub proof ck : Slice U8) :
 LIBB_ObservationModel.law pub proof ck env (run env pub proof ck) :=
 LIBB_ObservationModel.contains_graph env pub proof ck

/-- Both exit and chronology are computed on the complete input space. -/
theorem components (env : RSL.Env) (pub proof ck : Slice U8) :
 (run env pub proof ck).exit=NNC_WeakSpec.resultExit (LIBB_Tx2EnvCode.code env pub proof ck) ∧
 (run env pub proof ck).events=LIBB_Tx2EnvTrace.events env pub proof ck :=
 ⟨LIBB_ObservationModel.observation_exit env pub proof ck,
  LIBB_ObservationModel.result_events _ _⟩

/-- Successful parsing reaches the full common computation, retaining its
actual successful-resume suffix, errors and digest chronology. -/
theorem entered (env : RSL.Env) (pub proof ck : Slice U8)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok v)) :
 run env pub proof ck=
 LIB_Carriers.resultObs LIBB_ObservationModel.convert
  (LIBB_Tx2EnvTrace.common env pub proof ck)
  (LIBB_Tx2EnvCode.common env pub proof ck) :=
 LIBB_ObservationModel.parsed_observation env pub proof ck v parsed
#print axioms canonical
#print axioms components
#print axioms entered
end AspisR1.NNH_064SourceTotal
