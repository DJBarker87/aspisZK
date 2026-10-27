import R1Z.PV_RunJoin_NullifierLoop17
import R1Z.PV_RunJoin_ReferenceFixtureResults
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NullifierSource17
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_RunJoin_NullifierData17 PV_RunJoin_NullifierControl17

local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

def input : Slice U32 := ⟨key.val ++ salt.val,by
  rw [List.length_append,key.property,salt.property]
  scalar_tac⟩

theorem pipeline (k s : Array U32 8#usize) :
    pool_v1.format.pool_v1_nullifier (sourceExternalLinear := PV_Src_ExternalReference.dictionary) k s =
    (do
      let xs ← lift (Array.to_slice (BuilderNullifierReference.preimage k s))
      poseidon2.hash_fields (sourceExternalLinear := PV_Src_ExternalReference.dictionary) spend.DOMAIN_NULLIFIER xs) := by
  simp only [pool_v1.format.pool_v1_nullifier,spend.derive_nullifier,
    spend.nullifier_reference.derive_nullifier_owned,
    spend.nullifier_reference.derive_nullifier_owned_with,
    PV_RunJoin_HashCallback17.preimage,bind_tc_ok]
  change (do
    let (d,_) ← (BuiltinFnMut (U32 × Array U32 16#usize) (Array U32 8#usize)).call_mut
      (fun p => spend.nullifier_reference.hash_owned p.1 p.2)
      (spend.DOMAIN_NULLIFIER,BuilderNullifierReference.preimage k s)
    ok d) = spend.nullifier_reference.hash_owned spend.DOMAIN_NULLIFIER (BuilderNullifierReference.preimage k s)
  simp only [BuiltinFnMut]
  cases h : spend.nullifier_reference.hash_owned spend.DOMAIN_NULLIFIER (BuilderNullifierReference.preimage k s) <;> simp [h]
#print axioms pipeline

theorem hash_shape :
    poseidon2.hash_fields (sourceExternalLinear := PV_Src_ExternalReference.dictionary) 1095958530#u32 input =
    (do
      let state ← poseidon2.hash_fields_with_trace_loop0
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback PV_RunJoin_NullifierLoop17.iter0 () initial
      core.array.from_fn 8#usize
        (poseidon2.hash_fields_with_trace.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31 callback) state) := by
  unfold poseidon2.hash_fields poseidon2.hash_fields_with_trace
  simp only [poseidon2.RATE,aspis_core.field.M31.ZERO]
  have hr : Usize.wrapping_add 8#usize 1#usize = 9#usize := by
    apply UScalar.eq_of_val_eq
    rw [uadd _ _ (by simp)]
    rfl
  rw [hr]
  have len : input.len = 16#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val]
    rfl
  rw [len]
  simp only [core.slice.Slice.is_empty,core.slice.Slice.chunks,lift,bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ _ _ (by decide)]
  simp only [bind_tc_ok]
  rw [Array.index_mut_usize,index_ok _ 9#usize (by decide)]
  simp only [bind_tc_ok]
  have empty : input.length = 16 := rfl
  rw [empty]
  simp only [Nat.reduceEqDiff,decide_false,Bool.false_eq_true,ite_false]
  simp only [BuilderForestStd.chunks,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,UScalar.ofNatCore_val_eq, Nat.reduceEqDiff,ite_false,bind_tc_ok]
  have cast16 : UScalar.cast .U32 (16#usize) = 16#u32 := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  rw [cast16]
  have init : ((Array.repeat 16#usize 0#u32).set 8#usize 1095958530#u32).set 9#usize 16#u32 = initial := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have hlt : j < 16 := by simpa using hj
    interval_cases j <;> rfl
  rw [init]
  rfl
#print axioms hash_shape

theorem digest : core.array.from_fn 8#usize
    (poseidon2.hash_fields_with_trace.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31 callback) s5_23 =
    ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  with_unfolding_all rfl
#print axioms digest

theorem source : pool_v1.format.pool_v1_nullifier
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) key salt =
    ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  rw [pipeline]
  with_unfolding_all change poseidon2.hash_fields (sourceExternalLinear := PV_Src_ExternalReference.dictionary) 1095958530#u32 input = _
  rw [hash_shape,PV_RunJoin_NullifierLoop17.first]
  simp only [bind_tc_ok]
  exact digest
#print axioms source

theorem transfer : pool_v1.format.pool_v1_nullifier
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_RunJoin_FixtureArguments.witness.pair.nullifier_key
    PV_RunJoin_FixtureArguments.witness.pair.salt =
    ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  exact source
#print axioms transfer
theorem withdrawal : pool_v1.format.pool_v1_nullifier
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_RunJoin_FixtureArguments.witness.pair.nullifier_key
    PV_RunJoin_FixtureArguments.witness.pair.salt =
    ok PV_RunJoin_RecordedWithdrawal.publicRecord.nullifier := by
  exact source
#print axioms withdrawal
end R1Z.PV_RunJoin_NullifierSource17
