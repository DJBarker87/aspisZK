import ExtractedPreparationSerializerWhole
set_option autoImplicit false
namespace AspisR1.JFs_SerializerReflect
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (encoded : alloc.vec.Vec U8)
    (old : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (SerializerWhole.toOld pub)=ok (.Ok encoded)) :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded) := by
  have eq:=SerializerWhole.serializer_eq pub
  rw [old] at eq
  cases call : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub with
  | fail e => simp only [call,SerializerWhole.mapOutcome] at eq;cases eq
  | div => simp only [call,SerializerWhole.mapOutcome] at eq;cases eq
  | ok result =>
    cases result with
    | Err e => simp only [call,SerializerWhole.mapOutcome,SerializerFields.mapStatus] at eq;cases eq
    | Ok value =>
      simp only [call,SerializerWhole.mapOutcome,SerializerFields.mapStatus] at eq
      cases eq
      rfl

#print axioms source
end AspisR1.JFs_SerializerReflect
