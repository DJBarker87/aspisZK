import S1OwnedQueryWordStdV1
import Query31ExplicitListLoop
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody Query31ExplicitListLoop

def pack (s : Query31ExplicitScanBody.CurrentScan) (stop : Bool) : AspisS1OwnedQueryBlock.Total.Output :=
  (s.accepted,s.accepted_len,s.draws,stop)

/-- Complete retained emitted scanner-body sequence with the concrete Std
operations and one available iterator word. The native iterator is not replaced
or claimed installed by this definition. -/
def sourceWord (s : Query31ExplicitScanBody.CurrentScan) (candidate : U32) :
    Result AspisS1OwnedQueryBlock.Total.Output := do
  let cf ← body (stdOps listNext) [candidate] s
  match cf with
  | .cont (_,after) => ok (pack after false)
  | .done (after,_) => ok (pack after true)

private def bodyOne (s : Query31ExplicitScanBody.CurrentScan) (candidate : U32) :
    Result (ControlFlow (List U32 × Query31ExplicitScanBody.CurrentScan)
      (Query31ExplicitScanBody.CurrentScan × Option Bool)) := do
  if s.accepted_len=22#usize then ok (.done (s,none))
  else if s.draws=64#usize then ok (.done (s,none))
  else
    let d ← s.draws+1#usize
    let sl ← core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      s.accepted {«end»:=s.accepted_len}
    let found ← core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate
    if found then ok (.cont ([],{s with draws:=d}))
    else
      let updated ← Array.update s.accepted s.accepted_len candidate
      let n ← s.accepted_len+1#usize
      ok (.cont ([],{accepted:=updated,accepted_len:=n,draws:=d}))

private theorem bodyOne_eq (s : Query31ExplicitScanBody.CurrentScan) (candidate : U32) :
    body (stdOps listNext) [candidate] s=bodyOne s candidate := rfl

/-- Exact full Result equality to the existing source-body interpretation.
No successful read/add/update/contains hypothesis or range premise is added. -/
theorem stdWord_eq_sourceWord (s : Query31ExplicitScanBody.CurrentScan) (candidate : U32) :
    stdWord s.accepted s.accepted_len s.draws candidate=sourceWord s candidate := by
  unfold sourceWord
  rw [bodyOne_eq]
  by_cases full : s.accepted_len=22#usize
  · simp only [stdWord,bodyOne,bind_tc_ok,if_pos full,pack]
  by_cases exhausted : s.draws=64#usize
  · simp only [stdWord,bodyOne,bind_tc_ok,if_neg full,if_pos exhausted,pack]
  simp only [stdWord,bodyOne,bind_tc_ok,if_neg full,if_neg exhausted,
    bind_assoc_eq]
  apply bind_congr
  intro d
  apply bind_congr
  intro sl
  apply bind_congr
  intro found
  cases found with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false,bind_assoc_eq]
    apply bind_congr
    intro updated
    apply bind_congr
    intro n
    rfl

/-- The same original scanner-body word uses the checked extracted owned step.
The only domain premise is its actual bounded prefix, not a caller law. -/
theorem owned_step_eq_sourceWord (s : Query31ExplicitScanBody.CurrentScan) (candidate : U32)
    (hlen : s.accepted_len.val≤22) :
    owned_step s.accepted s.accepted_len s.draws candidate=sourceWord s candidate :=
  (owned_step_eq_stdWord s.accepted s.accepted_len s.draws candidate hlen).trans
    (stdWord_eq_sourceWord s candidate)

#print axioms stdWord_eq_sourceWord
#print axioms owned_step_eq_sourceWord
end AspisS1OwnedQueryBlock.Meaning
