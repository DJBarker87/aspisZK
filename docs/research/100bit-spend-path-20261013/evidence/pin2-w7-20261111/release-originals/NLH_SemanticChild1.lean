import NLH_SemanticState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticChild1
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
theorem step (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) (st : State) (before : st.packed=p.schedule) :
 NLH_SemanticState.step pub o s (.child 1) st=ok {st with packed := p.path} := by
 change (do let packed ← add_path_lanes st.packed o s;ok {st with packed := packed})=_
 rw [before,p.path_call,bind_tc_ok]
#print axioms step
end AspisR1.NLH_SemanticChild1
end
