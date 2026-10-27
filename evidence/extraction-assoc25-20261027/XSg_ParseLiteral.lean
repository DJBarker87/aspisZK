import XSe_ParseFinish
import XRx_TryDriver
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_ParseLiteral
abbrev OldPrefix := AspisR1PrefixAggregateParser.r1_wire.Prefix
abbrev OldError := AspisR1PrefixAggregateParser.r1_wire.Error
/-- The old parser's source-shaped record stage. -/
def stage (bytes : Slice U8) (i : Nat) (s : XRz_ParseFold.State) :
 Result (core.result.Result XRz_ParseFold.State OldError) := XSe_ParseStages.oldStep bytes i s
/-- Reuse the single inherited generic first-stop theorem, with this parser's
error, state, stage and final continuation. No separately unrolled driver law. -/
theorem driver (bytes : Slice U8) (root : Array U8 32#usize) (n i : Nat) (s : XRz_ParseFold.State) :
 (do let out ← XRx_TryDriver.run (stage bytes) i n s
     match out with | .Err e => ok (core.result.Result.Err e : core.result.Result OldPrefix OldError) | .Ok s => XSe_ParseFinish.finish bytes root s)=
 (do let out ← XRx_StageFold.fold (stage bytes) (List.range' i n) (.Ok s)
     match out with | .Err e => ok (core.result.Result.Err e : core.result.Result OldPrefix OldError) | .Ok s => XSe_ParseFinish.finish bytes root s) := by
 rw [XRx_TryDriver.source]
#print axioms driver
end XSg_ParseLiteral
