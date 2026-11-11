import NLH_SemanticState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticChild3
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
theorem step (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) (st : State) (before : st.packed=p.value) :
 NLH_SemanticState.step pub o s (.child 3) st=ok {st with packed := p.occupancy} := by
 change (do let packed ← add_occupancy_lanes st.packed pub o s;ok {st with packed := packed})=_
 rw [before,p.occupancy_call,bind_tc_ok]
#print axioms step
end AspisR1.NLH_SemanticChild3
end
