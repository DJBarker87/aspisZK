import XSg_OldCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldResume
open XSg_ParseLiteral
/-- One instance of the inherited generic first-stop driver, preserving the
literal old finishing continuation and the full carrier. -/
def run (bytes : Slice U8) (root : Array U8 32#usize) (i n : Nat)
 (s : XRz_ParseFold.State) : Result (core.result.Result OldPrefix OldError) := do
 let out ← XRx_TryDriver.run (stage bytes) i n s
 match out with | .Err e => ok (.Err e) | .Ok state => XSe_ParseFinish.finish bytes root state
/-- A single source stage with its recursive suffix opaque. -/
theorem advance (bytes : Slice U8) (root : Array U8 32#usize) (i n : Nat)
 (records : List (Slice U8)) (offset : Usize) :
 run bytes root i (n+1) (records,offset)=(do
  let r ← AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes (XRz_ParseFold.row i) offset
  match r with
  | .Err e => ok (.Err e)
  | .Ok p => run bytes root (i+1) n (records++[p.1],p.2)) := by
 unfold run
 rw [XRx_TryDriver.run]
 unfold stage XSe_ParseStages.oldStep
 cases h : AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes (XRz_ParseFold.row i) offset with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl
#print axioms advance
end XSg_OldResume
