import R1Z.PV_RunJoin_CallbackPermutation16
import R1Z.BuilderNullifierReference
set_option autoImplicit false
namespace R1Z.PV_RunJoin_HashCallback17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep

abbrev callback := poseidon2.hash_fields_with_trace.closure_1.Insts.CoreOpsFunctionFnMutTuplePoseidon2RoundTransitionTuple
  poseidon2.hash_fields.closure.Insts.CoreOpsFunctionFnMutPairUsizePoseidon2RoundTransitionTuple

theorem constant (index : Usize) (event : poseidon2.Poseidon2RoundTransition) :
    callback.call_mut ((),index) event = ok ((),((),index)) := by rfl

theorem permutation {K : Type} [Field K] [CharP K 2147483647] (index : Usize) (s : State) :
    ∃ out : State,
      poseidon2.permute_optimized_with_trace_threaded
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback s ((),index) = ok (out,((),index)) ∧
      Canonical out ∧ liftA (K := K) out = R0P.poseidonPermutation (liftA s) :=
  PV_RunJoin_CallbackPermutation16.source callback ((),index) (constant index) s

theorem preimage (key salt : Array U32 8#usize) :
    spend.nullifier_reference.preimage_owned key salt = ok (BuilderNullifierReference.preimage key salt) := by
  with_unfolding_all exact BuilderNullifierReference.preimage_owned_eq key salt
#print axioms constant
#print axioms permutation
#print axioms preimage
end R1Z.PV_RunJoin_HashCallback17
