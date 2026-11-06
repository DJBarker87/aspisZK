import NLH_CompositionState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompPoseidon
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
/-- Deterministic308 at the SAME produced openings/selectors. -/
theorem step (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (st : State)
 (ho : st.openings=⟨p.z,p.succ,p.xor12⟩) (hs : st.poseidonSelectors=p.poseidonSelectors) :
 NLH_CompositionState.step pub claims point lambda chi theta .poseidon st=ok (.Ok {st with poseidon := p.poseidon}) := by
 have call : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected st.openings st.poseidonSelectors=ok p.poseidon := by
   rw [ho,hs];exact p.poseidonCall
 change (do let a ← state_only_poseidon.evaluate_state_only_poseidon_oracle_projected st.openings st.poseidonSelectors
            ok (.Ok {st with poseidon := a}))=_
 rw [call,bind_tc_ok]
#print axioms step
end AspisR1.NLH_CompPoseidon
end
