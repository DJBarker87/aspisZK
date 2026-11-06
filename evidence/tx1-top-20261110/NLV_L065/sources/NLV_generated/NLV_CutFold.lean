import NLV_State
import NLV_Algebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect (Code)
/-- A proposed per-occurrence physical cut: native admission is NOT inferred
from this record. The Kani packet must realize all these fields on the SAME
pre/post state. No heap/payload conclusion follows from an address alone. -/
structure Cut (cfg : NLJ_Tx1.Configuration)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (s after : State) (reply : Result NLJ_Tx1.Post) (log : SdkC_Source.Log) : Prop where
 source : NHZ_DRIVER.Cuts hashv (NLJ_Tx1.step cfg s.core) reply log
 external : after.external=s.external
 inputs : after.core.input=s.core.input
 effects : after.attempted=s.attempted++log
/-- ONE native parent chain. Each next state is the SAME state returned by
its preceding occurrence; Err is a returned terminal, while fail/div have no
suffix. The physical Cut producer remains an OPEN obligation. -/
inductive Invocation (cfg : NLJ_Tx1.Configuration)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
 Nat → State → Result NLJ_Tx1.Out → SdkC_Source.Log → List Event → State → Prop where
 | returned {n : Nat} {s after : State} {out : NLJ_Tx1.Out} {log : SdkC_Source.Log}
   (head : Cut cfg hashv s after (ok (.inl out)) log) :
   Invocation cfg hashv (n+1) s (ok out) log [event s] after
 | next {n : Nat} {s middle last : State} {out : Result NLJ_Tx1.Out}
   {log suffix : SdkC_Source.Log} {events : List Event}
   (head : Cut cfg hashv s middle (ok (.inr middle.core)) log)
   (tail : Invocation cfg hashv n middle out suffix events last) :
   Invocation cfg hashv (n+1) s out (log++suffix) (event s::events) last
 | fail {n : Nat} {s after : State} {error : Error} {log : SdkC_Source.Log}
   (head : Cut cfg hashv s after (fail error) log) :
   Invocation cfg hashv (n+1) s (fail error) log [event s] after
 | div {n : Nat} {s after : State} {log : SdkC_Source.Log}
   (head : Cut cfg hashv s after div log) :
   Invocation cfg hashv (n+1) s div log [event s] after
/-- NHZ induction; this is a parameterized fold, NEVER a native row root. -/
theorem source_cuts {cfg : NLJ_Tx1.Configuration}
 {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {n : Nat} {s last : State} {out : Result NLJ_Tx1.Out}
 {log : SdkC_Source.Log} {events : List Event}
 (cuts : Invocation cfg hashv n s out log events last) :
 NHZ_DRIVER.Cuts hashv (NLJ_Tx1.fold cfg n s.core) out log := by
 induction cuts with
 | @returned n s after out log head =>
   let k : NLJ_Tx1.Post → Code NLJ_Tx1.Out := fun post =>
    match post with | .inl value => pure value | .inr next => NLJ_Tx1.fold cfg n next
   have tail : NHZ_DRIVER.Cuts hashv (k (.inl out)) (ok out) [] :=
    NHZ_DRIVER.Cuts.leaf (NGQ_Cuts.Trace.done out)
   simpa only [NLJ_Tx1.fold,List.append_nil,k,Bind.bind,Pure.pure] using
    (NHZ_DRIVER.Cuts.next (k:=k) head.source tail)
 | next head tail ih => exact NHZ_DRIVER.Cuts.next head.source ih
 | fail head => exact NHZ_DRIVER.Cuts.fail head.source _
 | div head => exact NHZ_DRIVER.Cuts.div head.source _
theorem external_frame_chain {cfg : NLJ_Tx1.Configuration}
 {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {n : Nat} {s last : State} {out : Result NLJ_Tx1.Out}
 {log : SdkC_Source.Log} {events : List Event}
 (cuts : Invocation cfg hashv n s out log events last) : last.external=s.external := by
 induction cuts with
 | returned h => exact h.external
 | next h _ ih => exact ih.trans h.external
 | fail h => exact h.external
 | div h => exact h.external
theorem input_frame_chain {cfg : NLJ_Tx1.Configuration}
 {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {n : Nat} {s last : State} {out : Result NLJ_Tx1.Out}
 {log : SdkC_Source.Log} {events : List Event}
 (cuts : Invocation cfg hashv n s out log events last) : last.core.input=s.core.input := by
 induction cuts with
 | returned h => exact h.inputs
 | next h _ ih => exact ih.trans h.inputs
 | fail h => exact h.inputs
 | div h => exact h.inputs
theorem effects {cfg : NLJ_Tx1.Configuration}
 {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {n : Nat} {s last : State} {out : Result NLJ_Tx1.Out}
 {log : SdkC_Source.Log} {events : List Event}
 (cuts : Invocation cfg hashv n s out log events last) : last.attempted=s.attempted++log := by
 induction cuts with
 | returned h => exact h.effects
 | next h _ ih => rw [ih,h.effects,List.append_assoc]
 | fail h => exact h.effects
 | div h => exact h.effects
#print axioms source_cuts
#print axioms external_frame_chain
#print axioms input_frame_chain
#print axioms effects
set_option pp.proofs false
#print source_cuts
end AspisR1.NLV
end
