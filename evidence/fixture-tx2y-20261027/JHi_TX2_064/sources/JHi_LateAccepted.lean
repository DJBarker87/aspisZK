import JHi_LateChildSpecs
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
  unfold encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)
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
