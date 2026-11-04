import NGD_AtCut
import NGD_ParseReference
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_AtReference
open NGD_ParseReference

def parser (reply : core.result.Result Unit NGD_AtG.Error) (row : U8) (bytes : Slice U8) :=
  NGD_ParseCut.invoke (fun _ _ => ok (NGD_ErrorPort.mapError reply)) row bytes

/-- The parent returns the original framed slice and same end offset, forwarding
all child errors. Arithmetic safety is an input-domain fact, never acceptance. -/
theorem forward (row tag : U8) (size length finish offset : Usize) (bytes : Slice U8)
    (reply : core.result.Result Unit NGD_AtG.Error)
    (shape : NGD_AtG.shape row = ok (some (tag,size)))
    (lengthAdd : 5#usize + size = ok length) (endAdd : offset + length = ok finish) :
    mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_at_g bytes row offset reply) =
      NGD_AtCut.invoke (parser reply) bytes row offset := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)) := by
    rw [← NGD_AtShape.reference]; exact shape
  have wlen := wrap_checked 5#usize size length lengthAdd
  have wend := wrap_checked offset length finish endAdd
  unfold NGD_AtG.parse_at_g NGD_AtCut.invoke
  simp only [shape,sourceShape,core.option.Option.unwrap,bind_tc_ok,lift,wlen,wend,lengthAdd,endAdd]
  try dsimp only
  try simp only [wlen,wend,lengthAdd,endAdd,lift,bind_tc_ok]
  cases get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=finish} with
  | fail e => simp [get,mapResult]
  | div => simp [get,mapResult]
  | ok framed =>
    cases framed with
    | none =>
      simp [get,NGD_AtG.core.option.Option.ok_or,
        AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        mapResult,NGD_ErrorPort.mapError,NGD_ErrorPort.toWire]
    | some original =>
      have child := NGD_ParseReference.all_inputs row original reply
      change mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_g row original reply) = parser reply row original at child
      simp only [get,NGD_AtG.core.option.Option.ok_or,
        AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      rw [← child]
      cases result : NGD_AtG.parse_g row original reply with
      | fail e => simp [mapResult]
      | div => simp [mapResult]
      | ok outcome =>
        cases outcome <;> simp [mapResult,NGD_ErrorPort.mapError,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms forward
end NGD_AtReference
