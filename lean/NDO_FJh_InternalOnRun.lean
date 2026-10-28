import RPv_FJh_InternalPairValue
import RPv_FJa_PoseidonOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
/-- The internal-pair VALUE from the evaluator's SAME actual openings and
selector interpolation; no independent child success is a hypothesis. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hs : canonical s.local)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    ∃ internal : Array NQ 16#usize,
      state_only_poseidon.interpolated_internal_pair o.z s.local=ok internal ∧
      canonical internal ∧ decoded internal=
        R0P.poseidonInterpolatedInternalPair (decoded o.z) (decoded s.local) := by
  obtain ⟨_,_,_,_,_,internal,_,_,_,_,_,_,_,ri,_,_,_⟩ := FJa_PoseidonOrigins.reached o s out run
  exact ⟨internal,ri,FJh_InternalPairValue.value o.z s.local internal hz hs ri⟩
#print axioms value
end AspisR1.FJh_InternalOnRun
end
