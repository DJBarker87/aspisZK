import R1Z.ProverRwQueryBlock
import R1Z.ProverRwQueryFinishTransport
set_option autoImplicit false
namespace R1Z.ProverRwQueryPolicy
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryBlock ProverRwQueryStop ProverRwQuerySourceWindow ProverRwQueryFinishTransport
open Query31ExplicitScanBody
open Query31ModelScanCall Query31ConcreteWordsDriverChain

set_option backward.isDefEq.respectTransparency false in
theorem raw_transport (blocks advances : Blocks) :
    host_transcript.queries_from_pairs blocks advances =
      (ProverCommitQuery26.raw blocks advances >>= fun r => ok (rawResult r)) := by
  change run blocks advances ProverCommitQuery26.initial = _
  unfold ProverCommitQuery26.raw AspisR1Query31Transcript.queries_from_pairs_with_scan
  have hb0 := ProverCommitArrayIndex25.array_index_usize_ok blocks 0#usize (by decide)
  obtain ⟨stop0,s1,hscan0,valid1,hsource0,end0⟩ :=
    block_source blocks advances 0#usize ProverCommitQuery26.initial (by decide) (by rfl) (by decide)
  rw [hsource0,hb0]
  simp only [bind_tc_ok]
  rw [hscan0]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop0 with
  | true =>
    change finishAt advances 0#usize s1 =
      (AspisR1Query31Transcript.finishAdvance advances 0#usize s1 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 0#usize s1).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb1 := ProverCommitArrayIndex25.array_index_usize_ok blocks 1#usize (by decide)
  obtain ⟨stop1,s2,hscan1,valid2,hsource1,end1⟩ :=
    block_source blocks advances 1#usize s1 (by decide) (by have h:=end0 rfl; simpa using h) valid1.1
  rw [hsource1,hb1]
  simp only [bind_tc_ok]
  rw [hscan1]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop1 with
  | true =>
    change finishAt advances 1#usize s2 =
      (AspisR1Query31Transcript.finishAdvance advances 1#usize s2 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 1#usize s2).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb2 := ProverCommitArrayIndex25.array_index_usize_ok blocks 2#usize (by decide)
  obtain ⟨stop2,s3,hscan2,valid3,hsource2,end2⟩ :=
    block_source blocks advances 2#usize s2 (by decide) (by have h:=end1 rfl; simpa using h) valid2.1
  rw [hsource2,hb2]
  simp only [bind_tc_ok]
  rw [hscan2]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop2 with
  | true =>
    change finishAt advances 2#usize s3 =
      (AspisR1Query31Transcript.finishAdvance advances 2#usize s3 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 2#usize s3).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb3 := ProverCommitArrayIndex25.array_index_usize_ok blocks 3#usize (by decide)
  obtain ⟨stop3,s4,hscan3,valid4,hsource3,end3⟩ :=
    block_source blocks advances 3#usize s3 (by decide) (by have h:=end2 rfl; simpa using h) valid3.1
  rw [hsource3,hb3]
  simp only [bind_tc_ok]
  rw [hscan3]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop3 with
  | true =>
    change finishAt advances 3#usize s4 =
      (AspisR1Query31Transcript.finishAdvance advances 3#usize s4 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 3#usize s4).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb4 := ProverCommitArrayIndex25.array_index_usize_ok blocks 4#usize (by decide)
  obtain ⟨stop4,s5,hscan4,valid5,hsource4,end4⟩ :=
    block_source blocks advances 4#usize s4 (by decide) (by have h:=end3 rfl; simpa using h) valid4.1
  rw [hsource4,hb4]
  simp only [bind_tc_ok]
  rw [hscan4]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop4 with
  | true =>
    change finishAt advances 4#usize s5 =
      (AspisR1Query31Transcript.finishAdvance advances 4#usize s5 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 4#usize s5).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb5 := ProverCommitArrayIndex25.array_index_usize_ok blocks 5#usize (by decide)
  obtain ⟨stop5,s6,hscan5,valid6,hsource5,end5⟩ :=
    block_source blocks advances 5#usize s5 (by decide) (by have h:=end4 rfl; simpa using h) valid5.1
  rw [hsource5,hb5]
  simp only [bind_tc_ok]
  rw [hscan5]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop5 with
  | true =>
    change finishAt advances 5#usize s6 =
      (AspisR1Query31Transcript.finishAdvance advances 5#usize s6 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 5#usize s6).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb6 := ProverCommitArrayIndex25.array_index_usize_ok blocks 6#usize (by decide)
  obtain ⟨stop6,s7,hscan6,valid7,hsource6,end6⟩ :=
    block_source blocks advances 6#usize s6 (by decide) (by have h:=end5 rfl; simpa using h) valid6.1
  rw [hsource6,hb6]
  simp only [bind_tc_ok]
  rw [hscan6]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop6 with
  | true =>
    change finishAt advances 6#usize s7 =
      (AspisR1Query31Transcript.finishAdvance advances 6#usize s7 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 6#usize s7).symm
  | false =>
  simp only [Bool.false_eq_true,if_false]
  have hb7 := ProverCommitArrayIndex25.array_index_usize_ok blocks 7#usize (by decide)
  obtain ⟨stop7,s8,hscan7,valid8,hsource7,end7⟩ :=
    block_source blocks advances 7#usize s7 (by decide) (by have h:=end6 rfl; simpa using h) valid7.1
  rw [hsource7,hb7]
  simp only [bind_tc_ok]
  rw [hscan7]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop7 with
  | true =>
    change finishAt advances 7#usize s8 =
      (AspisR1Query31Transcript.finishAdvance advances 7#usize s8 >>= fun r => ok (rawResult r))
    exact (finish_transport advances 7#usize s8).symm
  | false =>
    have cap : s8.draws=64#usize := by
      apply UScalar.eq_of_val_eq
      have h:=end7 rfl
      exact h
    have hr := run_at blocks advances 7#usize s8 (Or.inr cap) valid8.2.1 (by decide) (by rw [cap]; rfl)
    change run blocks advances s8 =
      (AspisR1Query31Transcript.finishAdvance advances 7#usize s8 >>= fun r => ok (rawResult r))
    exact hr.trans (finish_transport advances 7#usize s8).symm

theorem policy_transport (blocks advances : Blocks) :
    host_transcript.queries_from_pairs blocks advances =
      (ProverCommitQuery26.policy.queries blocks advances >>= fun r => ok (policyResult r)) := by
  rw [query_transport]
  exact raw_transport blocks advances

#print axioms raw_transport
#print axioms policy_transport
end R1Z.ProverRwQueryPolicy
