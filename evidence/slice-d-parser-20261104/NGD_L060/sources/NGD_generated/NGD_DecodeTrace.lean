import NGD_DecodeValueLaw
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace NGD_DecodeTrace
open AspisR1DecodeKFullV10
abbrev Q := aspis_core.field.QM31
abbrev Record := r1_wire.ValidatedRecord
abbrev Range := core.ops.range.Range Usize
abbrev Final (N : Usize) := Array Q N × Option (core.result.Result (Array Q N) r1_wire.Error)

structure Domain (N : Usize) (r : Record) (off byteOffset : Usize) : Prop where
  minlen : 5≤r.framed.val.length
  cap : r.framed.val.length≤3717
  start : byteOffset.val=32*off.val
  positive : 0<N.val
  range : 32*off.val+32*N.val≤r.framed.val.length-5

noncomputable def answer {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (index : Usize) (live : index.val<N.val) :=
  NGD_DecodeValueLaw.expected r off N index d.minlen d.cap d.positive live d.range

/-- One actual emitted iteration after the byte-window and Q leaf substitutions. -/
theorem step {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (iter nextIter : Range) (index : Usize)
    (out : Array Q N) (live : index.val<N.val)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some index,nextIter)) :
    r1_wire.ValidatedRecord.decode_k_loop.body r r.row off byteOffset iter out =
      match answer d index live with
      | .Ok q => do
          let updated ← Array.update out index q
          ok (.cont (nextIter,updated))
      | .Err e => ok (.done (out,some (.Err e))) := by
  have value : r1_wire.ValidatedRecord.decode_k_value {r with row:=r.row} byteOffset index off =
      ok (answer d index live) := by
    simpa only [answer] using NGD_DecodeValueLaw.value r off byteOffset N index
      d.minlen d.cap d.start d.positive live d.range
  have eta : ({row:=r.row,framed:=r.framed} : Record) = r := by cases r; rfl
  simp only [r1_wire.ValidatedRecord.decode_k_loop.body,next,bind_tc_ok,eta,value]
  cases h : answer d index live <;>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Trace contains only source-next, one decoded value and one typed write;
there is no whole-output equality or accepted execution among its fields. -/
inductive Trace {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) : Range → Array Q N → Final N → Prop where
  | done (iter : Range) (out : Array Q N)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (none,iter)) :
      Trace d iter out (out,none)
  | reject (iter nextIter : Range) (index : Usize) (out : Array Q N)
      (live : index.val<N.val)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some index,nextIter))
      (error : r1_wire.Error) (reply : answer d index live = .Err error) :
      Trace d iter out (out,some (.Err error))
  | write (iter nextIter : Range) (index : Usize) (out updated : Array Q N)
      (live : index.val<N.val)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some index,nextIter))
      (q : Q) (reply : answer d index live = .Ok q)
      (store : Array.update out index q = ok updated) (final : Final N)
      (rest : Trace d nextIter updated final) : Trace d iter out final

/-- Lean induction threads the same source/native per-value observations,
including the first error terminal and no invented suffix writes. -/
theorem loop {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (iter : Range) (out : Array Q N) (final : Final N)
    (trace : Trace d iter out final) :
    r1_wire.ValidatedRecord.decode_k_loop r iter r.row off byteOffset out = ok final := by
  induction trace with
  | done iter out next =>
    unfold r1_wire.ValidatedRecord.decode_k_loop
    apply NCO_LoopSteps.loop_done
    simp [r1_wire.ValidatedRecord.decode_k_loop.body,next]
  | reject iter nextIter index out live next error reply =>
    unfold r1_wire.ValidatedRecord.decode_k_loop
    apply NCO_LoopSteps.loop_done
    simpa only [reply] using step d iter nextIter index out live next
  | write iter nextIter index out updated live next q reply store final rest ih =>
    unfold r1_wire.ValidatedRecord.decode_k_loop at ih ⊢
    rw [NCO_LoopSteps.loop_continue _ (iter,out) (nextIter,updated) (by
      simpa only [reply,store,bind_tc_ok] using step d iter nextIter index out live next)]
    exact ih
#print axioms step
#print axioms loop
end NGD_DecodeTrace
