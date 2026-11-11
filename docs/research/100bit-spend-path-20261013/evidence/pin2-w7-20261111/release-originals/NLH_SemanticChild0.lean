import NLH_SemanticState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticChild0
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
theorem step (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) (st : State) (before : st.packed=NKR_TermSemanticSource.zero) :
 NLH_SemanticState.step pub o s (.child 0) st=ok {st with packed := p.schedule} := by
 change (do let packed ← add_schedule_lanes st.packed pub o s;ok {st with packed := packed})=_
 rw [before,p.schedule_call,bind_tc_ok]
#print axioms step
end AspisR1.NLH_SemanticChild0
end
