import XSg_ParseLiteral
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldParser
open XSg_ParseLiteral
/-- The parser's generic ordered driver with its literal header and finish. -/
def parse (bytes : Slice U8) : Result (core.result.Result OldPrefix OldError) := do
 if Slice.len bytes<32#usize then ok (.Err (.Length 0#u8)) else
 let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=32#usize}
 let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
 match r with
 | .Err _ => ok (.Err (.Length 0#u8))
 | .Ok root =>
  let out ← XRx_TryDriver.run (stage bytes) 0 27 ([],32#usize)
  match out with | .Err e => ok (.Err e) | .Ok s => XSe_ParseFinish.finish bytes root s
/-- Only the finite literal driver is installed here; all record calls and
unknown Results stay symbolic. The first-stop proof is generic (driver). -/
theorem source (bytes : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=parse bytes := by
 simp only [AspisR1PrefixAggregateParser.r1_wire.Prefix.parse,parse,
  XRx_TryDriver.run,stage,XSe_ParseStages.oldStep,XRz_ParseFold.row,
  Nat.reduceLT,_root_.dite_true,U8.ofNat,Nat.reduceAdd,
  bind_assoc_eq,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
  core.convert.FromSame.from,XSe_ParseFinish.finish]
 rfl
#print axioms source
end XSg_OldParser
