import AspisR1S9CurrentCheckpointKDecoderV1.Funs
import AspisR1DecodeKFullV10.Funs
import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentCheckpointKDecoderCMMapV1
abbrev CurCM := AspisR1S9CurrentCheckpointKDecoderV1.field.CM31
abbrev OldCM := AspisR1DecodeKFullV10.aspis_core.field.CM31

def toOldCM (q : CurCM) : OldCM := ⟨q.a,q.b⟩
abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl
private theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    mapResult f (Bind.bind r k) = Bind.bind r (fun x => mapResult f (k x)) := by
  cases r <;> rfl
private theorem mapResult_option_case {A B C : Type} (f : B → C) (o : Option A)
    (noneCase : Result B) (someCase : A → Result B) :
    mapResult f (match o with | none => noneCase | some x => someCase x) =
      (match o with | none => mapResult f noneCase | some x => mapResult f (someCase x)) := by
  cases o <;> rfl
private theorem mapResult_result_case {A E B C : Type} (f : B → C)
    (r : core.result.Result A E) (okCase : A → Result B) (errCase : E → Result B) :
    mapResult f (match r with | .Ok x => okCase x | .Err e => errCase e) =
      (match r with | .Ok x => mapResult f (okCase x) | .Err e => mapResult f (errCase e)) := by
  cases r <;> rfl

theorem current_option_try_match {A B : Type} (value : Option A)
    (next : A → Result (Option B)) :
    (do
      let cf ← AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch value
      match cf with
      | .Continue x => next x
      | .Break residual =>
        AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual) =
      (match value with | none => .ok none | some x => next x) := by
  cases value <;> rfl

theorem old_option_try_match {A B : Type} (value : Option A)
    (next : A → Result (Option B)) :
    (do
      let cf ← AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitTry.branch value
      match cf with
      | .Continue x => next x
      | .Break residual =>
        AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual) =
      (match value with | none => .ok none | some x => next x) := by
  cases value <;> rfl

/-- Same actual four-byte M31 decoder, with only its nominal owner changed. -/
theorem m31_decoder_same (bytes : Array U8 4#usize) :
    AspisR1S9CurrentCheckpointKDecoderV1.field.M31.from_le_bytes bytes =
      AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes := by
  unfold AspisR1S9CurrentCheckpointKDecoderV1.field.M31.from_le_bytes
    AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes
    AspisR1S9CurrentCheckpointKDecoderV1.field.P AspisR1DecodeKFullV10.aspis_core.field.P
  rfl

/-- Full Result/Option transport, including every slice/array rejection and
outer failure/divergence. No successful decoder or input-width premise. -/
theorem cm_decoder_map (bytes : Slice U8) :
    mapResult (Option.map toOldCM)
      (AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes bytes) =
      AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes bytes := by
  simp only [AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes,
    AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes,
    current_option_try_match,old_option_try_match,m31_decoder_same,
    mapResult_bind,mapResult_option_case,mapResult_result_case,mapResult_ok,
    Option.map_none,Option.map_some,toOldCM] <;> rfl

#print axioms current_option_try_match
#print axioms old_option_try_match
#print axioms m31_decoder_same
#print axioms cm_decoder_map
end AspisR1S9CurrentCheckpointKDecoderCMMapV1
