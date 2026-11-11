import NLH_SemanticState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticChild2
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
theorem step (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) (st : State) (before : st.packed=p.path) :
 NLH_SemanticState.step pub o s (.child 2) st=ok {st with packed := p.value} := by
 change (do let packed ← add_value_lanes st.packed o s;ok {st with packed := packed})=_
 rw [before,p.value_call,bind_tc_ok]
#print axioms step
end AspisR1.NLH_SemanticChild2
end
