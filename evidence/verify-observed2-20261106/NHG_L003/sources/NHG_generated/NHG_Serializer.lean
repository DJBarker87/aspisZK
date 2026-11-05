import NGX_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_Serializer
open AspisR1PublicPreparation.SerializerFields
abbrev Public := pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Vec := alloc.vec.Vec U8

def restore {A : Type} : Result (core.result.Result A OldError) →
 Result (core.result.Result A NewError)
 | .ok (.Ok a) => .ok (.Ok a)
 | .ok (.Err e) => .ok (.Err (fromError e))
 | .fail e => .fail e
 | .div => .div

theorem restore_map {A : Type} (r : Result (core.result.Result A NewError)) :
 restore (SerializerWhole.mapOutcome r)=r := by
 cases r with
 | ok r => cases r with
   | Ok a => rfl
   | Err e => exact congrArg (fun e => Result.ok (core.result.Result.Err e)) (from_to_error e)
 | fail e => rfl
 | div => rfl

/-- The actual complete producer, with both Public variants and every outcome.
No selected successful serializer or unrelated public-byte value is a premise. -/
def computation (p : Public) : Result (core.result.Result Vec NewError) :=
 restore (AspisR1PublicSerializer.Whole431.program
  (AspisR1PublicSerializer.Whole431.sourceSteps (SerializerWhole.toOld p))
  (alloc.vec.Vec.new U8))

theorem source (p : Public) : p.public_bytes=computation p := by
 have eq:=SerializerWhole.serializer_eq p
 rw [AspisR1PublicSerializer.Whole431.source_eq_program] at eq
 have inv:=congrArg restore eq
 rw [restore_map] at inv
 exact inv.symm

/-- A selected canonical model output determines its full value, never just
its length or a digest. This is elimination, not an added success premise
in source: source above holds for every outcome. -/
theorem bytes (p : Public) (out : Vec) (h : p.public_bytes=ok (.Ok out)) :
 out.val=(AspisR1PublicSerializer.Whole431.sourceSteps
   (SerializerWhole.toOld p)).flatMap AspisR1PublicSerializer.Whole431.stepBytes := by
 have eq:=SerializerWhole.serializer_eq p
 rw [h] at eq
 have old : (SerializerWhole.toOld p).public_bytes=ok (.Ok out) := eq
 exact (AspisR1PublicSerializer.Whole431.source_success _ _ old).2

/-- Complete one-step emitted body transport on an arbitrary iterator and
arbitrary prior Vec, including rejection before appending and no append at end. -/
theorem field_body (it : Iter) (out : Vec) :
 AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out =
 mapFlow (pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body it out) :=
 fields_body_eq it out

#print axioms restore_map
#print axioms source
#print axioms bytes
#print axioms field_body
end AspisR1.NHG_Serializer
