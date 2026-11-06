import NJT_ClaimsRef_Code
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_ClaimsRef_Value
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent
open NJT_ClaimsRef_Code

/-- Returning standard allocation interpretation; allocator abort is retained
at the headline's Allocator boundary, never represented by a free Bool. -/
def std : ClaimsUnrolledFinish.StdCalls where
 reserve := fun _ v _ => ok (.Ok (),v)
 intoBox := fun _ v => ok v

def external : External := ClaimsUnrolledFinish.external std

def unbox (r : Result (core.result.Result (Slice Claims) r1_wire.Error)) : Result Status := do
 let result ← r
 match result with
 | .Err e => ok (.Err e)
 | .Ok s => match s.val with
   | [value] => ok (.Ok value)
   | _ => ok (.Err .Allocation)

def decode (pre : r1_wire.Prefix) : Result Status := do
 let r ← ClaimsUnrolledFinish.sourceRecord pre 25#u8
 match r with
 | .Err e => ok (.Err e)
 | .Ok record => decodeRows external record

theorem singleton_unbox (value : Claims) : unbox (ok (.Ok (NJT_ClaimsRef_Code.singleton value))) = ok (.Ok value) := rfl

/-- All source decoder rejection/fail/div branches are preserved. Allocation
value is installed, rather than a successful allocation outcome hypothesis. -/
theorem reference (pre : r1_wire.Prefix) :
 unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref pre) = decode pre := by
 cases h0 : ClaimsUnrolledFinish.sourceRecord pre 25#u8 with
 | fail error =>
   simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0]
 | div =>
   simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0]
 | ok r0 =>
   cases r0 with
   | Err error =>
     simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0]
   | Ok record =>
     cases h1 : ClaimsUnrolledFinish.sourceDecode 29#usize record 0#usize with
     | fail error =>
       simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1]
     | div =>
       simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1]
     | ok r1 =>
       cases r1 with
       | Err error =>
         simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1]
       | Ok row0 =>
         cases h2 : ClaimsUnrolledFinish.sourceDecode 29#usize record 29#usize with
         | fail error =>
           simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2]
         | div =>
           simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2]
         | ok r2 =>
           cases r2 with
           | Err error =>
             simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2]
           | Ok row1 =>
             cases h3 : ClaimsUnrolledFinish.sourceDecode 29#usize record 58#usize with
             | fail error =>
               simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2, h3]
             | div =>
               simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2, h3]
             | ok r3 =>
               cases r3 with
               | Err error =>
                 simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2, h3]
               | Ok row2 =>
                 simp [unbox, decode, NJT_ClaimsRef.r1_semantic.NJT_claims_ref, decodeRows, external, ClaimsUnrolledFinish.external, NJT_ClaimsRef.r1_wire.Prefix.validated_record, NJT_ClaimsRef.r1_wire.ValidatedRecord.decode_k, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, NJT_ClaimsRef_Code.filled_one, NJT_ClaimsRef.alloc.vec.Vec.into_boxed_slice, core.result.Result.map_err, AspisR1.Port4C_GeometryStd.mapError, NJT_ClaimsRef.r1_semantic.NJT_claims_ref.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once, NJT_ClaimsRef_Code.singleton, Array.make, h0, h1, h2, h3]

#print axioms singleton_unbox
#print axioms reference
end AspisR1.NJT_ClaimsRef_Value
end
