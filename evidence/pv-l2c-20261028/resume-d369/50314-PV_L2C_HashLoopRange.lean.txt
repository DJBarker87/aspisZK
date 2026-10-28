import PV_L2C_ChunkStep
set_option autoImplicit false
namespace PV_L2C_HashLoopRange
open Aeneas Aeneas.Std Result R1Z R1Z.BuilderForestStdPort
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

abbrev callback := poseidon2.hash_fields.closure.Insts.CoreOpsFunctionFnMutPairUsizePoseidon2RoundTransitionTuple

/-- On success, each completed hash permutation restores canonical raw state.
The loop proof covers arbitrary chunk contents and retains failing Result
branches; no field-model projection is used to infer a raw range. -/
theorem success (i : PV_L2C_ChunkStep.Iter) (state out : State)
    (hs : 0 < i.iter.size) (hc : Canonical state)
    (h : poseidon2.hash_fields_with_trace_loop0 callback i () state = ok out) :
    Canonical out := by
  generalize he : i.iter.remaining.val.length = n
  induction n using Nat.strong_induction_on generalizing i state out with
  | h n ih =>
    rw [poseidon2.hash_fields_with_trace_loop0.eq_1] at h
    pv_peel h with result hnext
    rcases result with ⟨o,j⟩
    cases o with
    | none =>
      cases h
      exact hc
    | some p =>
      obtain ⟨hsize,hlen⟩ := PV_L2C_ChunkStep.returned i j p hs hnext
      pv_peel h with sliceIter hsIter
      pv_peel h with enumeration henum
      pv_peel h with absorbed habsorbed
      obtain ⟨expected,hperm,hcan,_⟩ :=
        PV_RunJoin_HashCallback17.permutation (K := ZMod 2147483647) p.1 absorbed
      rw [hperm] at h
      change poseidon2.hash_fields_with_trace_loop0 callback j () expected = ok out at h
      exact ih j.iter.remaining.val.length (by omega) j expected out
        (by rw [hsize]; exact hs) hcan h rfl
#print axioms success
end PV_L2C_HashLoopRange
