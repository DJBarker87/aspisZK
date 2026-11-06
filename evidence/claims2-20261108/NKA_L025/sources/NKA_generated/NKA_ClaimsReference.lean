import NKA_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsReference
open Aeneas Aeneas.Std Result NJT_ClaimsRef

def reserveFilled {T : Type} (reservation : NP6_StdModel.Reservation)
 (copy : core.marker.Copy T) (n : Usize) (value : T) :
 Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) :=
 match reservation with
 | .Ok _ => NJT_ClaimsRef.aspis_core.r0.heap.filled copy n value
 | .Err _ => ok (.Err .Allocation)

/-- Exact E001 emitted reference body, with the already-external heap.filled
reserve interpretation installed AT ITS ORIGINAL SITE. No changed Rust body,
new extraction or extended ReviewedTranscription item. Successful reservation
reduces to the original emitted body; rejection is the allocator outcome. -/
def run (reservation : NP6_StdModel.Reservation)
  (prefix1 : r1_wire.Prefix) :
  Result (core.result.Result (Slice (Array (Array aspis_core.field.QM31
    29#usize) 3#usize)) r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 25#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 29#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r3 ← r1_wire.ValidatedRecord.decode_k 29#usize vr 58#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r4 ←
            reserveFilled reservation (Array.Insts.CoreMarkerCopy 3#usize
              (Array.Insts.CoreMarkerCopy 29#usize
              aspis_core.field.QM31.Insts.CoreMarkerCopy)) 1#usize
              (Array.make 3#usize [ val, val1, val2 ])
          let r5 ←
            core.result.Result.map_err
              r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
              r4 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let s ← alloc.vec.Vec.into_boxed_slice Global val3
            ok (core.result.Result.Ok s)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
              (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
            (core.convert.FromSame r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
          (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
        (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice (Array (Array aspis_core.field.QM31 29#usize) 3#usize))
      (core.convert.FromSame r1_wire.Error) residual


theorem emitted_success (pre : r1_wire.Prefix) :
 run (.Ok ()) pre = NJT_ClaimsRef.r1_semantic.NJT_claims_ref pre := by rfl

/-- Reinterpret only the existing external allocation site, preserving ALL
reference decoder rejections and ambient failures. No decoder success input. -/
theorem reference (reservation : NP6_StdModel.Reservation) (pre : r1_wire.Prefix) :
 NJT_ClaimsRef_Value.unbox (run reservation pre) =
 (do let decoded ← NJT_ClaimsRef_Value.decode pre
     match decoded with
     | .Err e => ok (.Err e)
     | .Ok value => NKA_ClaimsModel.reserveResult reservation value) := by
 cases reservation with
 | Ok unit =>
  cases unit
  rw [emitted_success,NJT_ClaimsRef_Value.reference]
  cases h : NJT_ClaimsRef_Value.decode pre with
  | fail e => rfl
  | div => rfl
  | ok result => cases result <;> rfl
 | Err e =>
  cases h0 : ClaimsUnrolledFinish.sourceRecord pre 25#u8 with
  | fail error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0]
  | div => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0]
  | ok result0 =>
   cases result0 with
   | Err error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0]
   | Ok record =>
    cases h1 : ClaimsUnrolledFinish.sourceDecode 29#usize record 0#usize with
    | fail error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1]
    | div => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1]
    | ok result1 =>
     cases result1 with
     | Err error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1]
     | Ok row1 =>
      cases h2 : ClaimsUnrolledFinish.sourceDecode 29#usize record 29#usize with
      | fail error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2]
      | div => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2]
      | ok result2 =>
       cases result2 with
       | Err error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2]
       | Ok row2 =>
        cases h3 : ClaimsUnrolledFinish.sourceDecode 29#usize record 58#usize with
        | fail error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2,h3]
        | div => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2,h3]
        | ok result3 =>
         cases result3 with
         | Err error => simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2,h3]
         | Ok row3 =>
          simp [run,NJT_ClaimsRef_Value.unbox,NJT_ClaimsRef_Value.decode,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,
  NJT_ClaimsRef.r1_wire.Prefix.validated_record,NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k,
  AspisR1ClaimsUnrolledParent.decodeRows,reserveFilled,NKA_ClaimsModel.reserveResult,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,h0,h1,h2,h3]

theorem parsed (reservation : NP6_StdModel.Reservation) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parser : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ value,
 NJT_ClaimsRef_Value.unbox (run reservation
   (ClaimsUnrolledFinish.fromMainPrefix (AspisR1PublicPreparation.PrefixAdapter.fromOld pre)))=
    NKA_ClaimsModel.reserveResult reservation value ∧
 AspisR1ClaimsUnrolledParent.candidate_claims.claims (NKA_Reservation.external reservation)
   (ClaimsUnrolledFinish.fromMainPrefix (AspisR1PublicPreparation.PrefixAdapter.fromOld pre))=
    NKA_ClaimsModel.reserveResult reservation value := by
 obtain ⟨value,pure,cohort⟩:=NKA_ClaimsModel.parsed reservation bytes pre parser
 refine ⟨value,?_,cohort⟩
 rw [reference]
 rw [NJT_ClaimsRef_Value.reference] at pure
 rw [pure]
 rfl

#print axioms reference
#print axioms parsed
#print axioms emitted_success
end AspisR1.NKA_ClaimsReference
end
