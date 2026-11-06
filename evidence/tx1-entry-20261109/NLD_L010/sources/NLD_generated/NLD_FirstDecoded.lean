import NLD_CutFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
/-- Literal source-order model program for frozen lib.rs:49-51. The child
returns its complete Result; only the Err arm invokes error mapping. These
source actions leave the extra heap carrier unchanged. Native post/frame
association is not asserted by this definition. -/
def firstDecoded (ops : AdapterRw.Ops) (semantic : Public)
    (publicBytes proof : Bytes) (split : Usize) : Program Reply :=
  .step .observer (fun s => (AdapterRw.observer ops,s)) fun observer _ =>
  .step .tx1 (fun s => (ops.op10
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    semantic publicBytes proof split () observer,s)) fun reply _ =>
    match reply with
    | .Ok checkpoint => .done (.Ok checkpoint)
    | .Err error =>
      .step .errorMap (fun s => (ops.op44 error,s)) fun mapped _ =>
        .done (.Err mapped)

/-- Exact emitted first_decoded Result, without a selected-success premise.
This is source erasure, not a native parent certificate or row root. -/
theorem firstDecoded_erasure (ops : AdapterRw.Ops) (semantic : Public)
    (publicBytes proof : Bytes) (split : Usize) (s : ParentState) :
    (run (firstDecoded ops semantic publicBytes proof split) s).1 =
      AdapterRw.first_decoded ops semantic publicBytes proof split := by
  unfold firstDecoded AdapterRw.first_decoded AdapterRw.observer
  simp only [run, bind_tc_ok]
  generalize ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    semantic publicBytes proof split () none = r
  cases r with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Ok checkpoint => rfl
    | Err error =>
      change (match ops.op44 error with
        | .ok mapped => .ok (core.result.Result.Err mapped)
        | .fail e => .fail e
        | .div => .div) =
        (do let mapped ← ops.op44 error
            ok (core.result.Result.Err mapped))
      cases ops.op44 error <;> rfl

/-- Source actions do not mutate the additional heap/borrow/owned carrier.
No statement about native SDK heap preservation is inferred from this fact. -/
theorem firstDecoded_source_frame (ops : AdapterRw.Ops) (semantic : Public)
    (publicBytes proof : Bytes) (split : Usize) (s : ParentState) :
    (run (firstDecoded ops semantic publicBytes proof split) s).2.1 = s := by
  unfold firstDecoded AdapterRw.observer
  simp only [run]
  generalize ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    semantic publicBytes proof split () none = r
  cases r with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Ok checkpoint => rfl
    | Err error =>
      simp only [run, bind_tc_ok]
      generalize ops.op44 error = mapped
      cases mapped <;> rfl
#print axioms firstDecoded_erasure
#print axioms firstDecoded_source_frame
end AspisR1.NLD
