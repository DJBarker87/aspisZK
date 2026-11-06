import NKI_InitialPrefix
import NLH_CompGathers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompPoseidonSelectors
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
theorem poseidon_selectors (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (st : State) (h : st.selectors=p.selectors) :
 step pub claims point lambda chi theta .poseidonSelectors st=ok (core.result.Result.Ok {st with poseidonSelectors := p.poseidonSelectors}) := by
 have call : pool_v1.pair_forest_semantic_terminal.poseidon_selectors st.selectors=ok p.poseidonSelectors := by
   rw [h];exact p.poseidonSelectorCall
 change (do let s ← pool_v1.pair_forest_semantic_terminal.poseidon_selectors st.selectors
            ok (core.result.Result.Ok {st with poseidonSelectors := s}))=_
 rw [call,bind_tc_ok]
#print axioms poseidon_selectors
end AspisR1.NLH_CompPoseidonSelectors
end
