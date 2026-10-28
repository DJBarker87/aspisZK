import NDO_JHi_LateChildSpecs
import AdapterRwScalar
set_option autoImplicit false
namespace AspisR1.JHi_LateAccepted
open Aeneas Aeneas.Std Result WP
open AspisR1AdapterReconstruct aspis_statement.pool_v1.pair_tree_profile

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property
#print axioms array_slice_length

theorem spec (output : Slice U8) (size : output.length=1520) :
    encode_pool_v1_pair_late_public_statement_v1 JHg_RawCommon.common.lane_transition output
      ⦃ result => result.1=core.result.Result.Ok () ∧ result.2.length=1520 ⦄ := by
  have bytes : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES=ok 1520#usize := by
    unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
      POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    rw [AdapterRw.Scalar.add_eq 32#usize 800#usize 832#usize (by decide),bind_tc_ok,
      AdapterRw.Scalar.add_eq 8#usize 680#usize 688#usize (by decide),bind_tc_ok,
      AdapterRw.Scalar.add_eq 832#usize 688#usize 1520#usize (by decide)]
  have afterbytes : aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize := by
    unfold aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    exact AdapterRw.Scalar.add_eq _ _ _ (by decide)
  have sizeU : Slice.len output=1520#usize := by scalar_tac
  have next : U64.checked_add JHg_RawCommon.common.lane_transition.live_snapshot.next_pair_index 1#u64=
      some JHg_RawCommon.common.lane_transition.candidate_afterstate.next_pair_index := rfl
  have compare : core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
      (some JHg_RawCommon.common.lane_transition.candidate_afterstate.next_pair_index)
      (some JHg_RawCommon.common.lane_transition.candidate_afterstate.next_pair_index)=ok false := rfl
  unfold encode_pool_v1_pair_late_public_statement_v1
  rw [bytes,bind_tc_ok,sizeU]
  simp only [show (1520#usize !=1520#usize)=false from rfl,Bool.false_eq_true,↓reduceIte]
  rw [next]
  simp only [lift,bind_tc_ok,compare,Bool.false_eq_true,↓reduceIte,bytes,afterbytes]
  unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)
  all_goals try simp_all only [core.result.Result.Insts.CoreOpsTry.branch]
  all_goals first
    | (have good := r3_post _ rfl; rw [good] at cf1_post; cases cf1_post)
    | (have good := r1_post () trivial; rw [good] at cf_post; cases cf_post)

#print axioms spec

theorem source (output : Slice U8) (size : output.length=1520) : ∃ updated : Slice U8,
    encode_pool_v1_pair_late_public_statement_v1 JHg_RawCommon.common.lane_transition output=
      ok (core.result.Result.Ok (),updated) ∧ updated.length=1520 := by
  obtain ⟨⟨status,updated⟩,run,success,len⟩:=WP.spec_imp_exists (spec output size)
  change status=core.result.Result.Ok () at success
  subst status
  exact ⟨updated,run,len⟩
#print axioms source
end AspisR1.JHi_LateAccepted
