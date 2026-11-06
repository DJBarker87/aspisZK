import NLH_CompGathers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompSelectors
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
theorem selectors (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (st : State) :
 step pub claims point lambda chi theta .selectors st=ok (.Ok {st with selectors := p.selectors}) := by
 change (do let s ← pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
            ok (.Ok {st with selectors := s}))=_
 rw [p.selectorCall,bind_tc_ok]
theorem poseidon_selectors (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (st : State) (h : st.selectors=p.selectors) :
 step pub claims point lambda chi theta .poseidonSelectors st=ok (.Ok {st with poseidonSelectors := p.poseidonSelectors}) := by
 have call : pool_v1.pair_forest_semantic_terminal.poseidon_selectors st.selectors=ok p.poseidonSelectors := by
   rw [h];exact p.poseidonSelectorCall
 change (do let s ← pool_v1.pair_forest_semantic_terminal.poseidon_selectors st.selectors
            ok (.Ok {st with poseidonSelectors := s}))=_
 rw [call,bind_tc_ok]
#print axioms selectors
#print axioms poseidon_selectors
end AspisR1.NLH_CompSelectors
end
