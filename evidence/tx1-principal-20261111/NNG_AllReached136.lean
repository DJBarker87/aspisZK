import NNG_DomRounds136
import NNG_ConcreteInput136
import NNG_TreeEmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_AllReached136
open Aeneas Aeneas.Std NNG_Emitted NNG_TraceAll136 NNG_TypedDomains136

/-- Every reached native-model child use has its actual input domain proved
from original inputs and CLOSED preceding returns, on this SAME full trace. -/
theorem all_calls (env : RSL.Env) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (challenges : LIB_VCarriers.Challenges) (obs : Observer)
    (publicDom : LIB_VPublicDomain.publicDom pub) :
    All Checked (NNG_FinishTree.tree (NNG_ConcreteCalls136.calls env) (NNG_ConcreteInput136.input pub p t challenges obs env)) := by
  rw [NNG_TreeEmission.tree_suffixes]
  exact NNG_DomRounds136.rounds challenges.eta (NNG_ConcreteCalls136.calls env) env (NNG_SourceCalls136.concrete env)
    (NNG_ConcreteInput136.input pub p t challenges obs env) p rfl pub rfl challenges rfl publicDom
#print axioms all_calls
end AspisR1.NNG_AllReached136
