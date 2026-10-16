import ExtractedPublicPreparationSuccess
import AspisR1PublicSerializer.Funs

/-! Fixed error transport between the two exact serializer extractions.
This first predecessor concerns their actual field-loop bodies; it does not
assume agreement of the complete serializers or of their Rust executions. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1PublicPreparation.SerializerFields
abbrev NewError := aspis_core.state_only_prefix.r0.Error
abbrev OldError := AspisR1PublicSerializer.aspis_core.state_only_prefix.r0.Error
abbrev ByteVec := alloc.vec.Vec U8
abbrev Iter := core.slice.iter.Iter U32
abbrev State := Iter × ByteVec

def toError : NewError → OldError
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row index => .NonCanonical row index
  | .Boundary index => .Boundary index
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

def fromError : OldError → NewError
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row index => .NonCanonical row index
  | .Boundary index => .Boundary index
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

theorem from_to_error (e : NewError) : fromError (toError e) = e := by
  cases e <;> rfl

theorem to_from_error (e : OldError) : toError (fromError e) = e := by
  cases e <;> rfl

def mapStatus {α : Type} : core.result.Result α NewError → core.result.Result α OldError
  | .Ok x => .Ok x
  | .Err e => .Err (toError e)

def mapPairOutcome {α : Type} : Result (core.result.Result α NewError × ByteVec) →
    Result (core.result.Result α OldError × ByteVec)
  | .ok (status, out) => .ok (mapStatus status, out)
  | .fail e => .fail e
  | .div => .div

def mapFlow : Result (ControlFlow State (core.result.Result Unit NewError × ByteVec)) →
    Result (ControlFlow State (core.result.Result Unit OldError × ByteVec))
  | .ok (.cont state) => .ok (.cont state)
  | .ok (.done (status, out)) => .ok (.done (mapStatus status, out))
  | .fail e => .fail e
  | .div => .div

/-- Complete one-step outcome equality; allocation failure/divergence and
the exact mutable output vector are preserved, not just successful bytes. -/
theorem fields_body_eq (it : Iter) (out : ByteVec) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out =
      mapFlow (pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out) := by
  unfold AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
  cases hnext : core.slice.iter.IteratorSliceIter.next it with
  | fail e => simp only [bind_tc_fail, mapFlow]
  | div => simp only [bind_tc_div, mapFlow]
  | ok pair =>
    rcases pair with ⟨value, next⟩
    cases value with
    | none => rfl
    | some value =>
      simp only [bind_tc_ok, AspisR1PublicSerializer.aspis_core.field.P,
        aspis_core.field.P]
      change (if value >= 2147483647#u32 then
          ok (done (core.result.Result.Err
            AspisR1PublicSerializer.aspis_core.state_only_prefix.r0.Error.Public, out))
        else do
          let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value))
          ok (cont (next, out1))) =
        mapFlow (if value >= 2147483647#u32 then
          ok (done (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public, out))
        else do
          let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value))
          ok (cont (next, out1)))
      split
      · rfl
      · cases he : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (core.num.U32.to_le_bytes value)) <;> rfl

#print axioms from_to_error
#print axioms to_from_error
#print axioms fields_body_eq
end AspisR1PublicPreparation.SerializerFields
