import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_DRIVER
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation

/-- Effect syntax for the three chronological calls in the delivered scalar
Block packet. This is local syntax; identification inside prepare is still OPEN. -/
def scalarBlockCode (before : transcript.Transcript Unit) (row : U8)
    (payload : Slice U8) : Code (Array U8 32#usize × transcript.Transcript Unit) :=
  .step (160#u8 + row) fun tag =>
    .read (NGT_NBA_Transcript.absorbParts before.state tag payload) fun absorbed =>
      .read (NGT_NBA_Transcript.readParts absorbed 1#u8) fun value =>
        .read (NGT_NBA_Transcript.readParts absorbed 2#u8) fun final =>
          .done (value,{before with state:=final})

/-- Full successful log, retaining all three occurrences, with no SHA evaluation.
The successful packet cannot certify stopped scalar invocations. -/
theorem scalar_block_cut
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (block : NGT_NBL_BlockTrace.Block (NGQ_Effects.dictionary hashv) before row payload) :
    Cuts hashv (scalarBlockCode before row payload) (.ok (block.value,block.after))
      (block.log.map fun e => (⟨e.1,.ok e.2⟩ : SdkC_Source.Query)) := by
  apply Cuts.leaf
  apply NGQ_Cuts.Trace.stepOk _ _ block.tag block.tagCall
  apply NGQ_Cuts.Trace.readOk _ _ block.absorbed block.absorbCall
  apply NGQ_Cuts.Trace.readOk _ _ block.value block.readCall
  apply NGQ_Cuts.Trace.readOk _ _ block.final block.advanceCall
  exact .done _

/-- Single unsuccessful syscall records its attempted address before returning;
there is no continuation invocation. Can be installed at every driver suffix. -/
theorem syscall_fail_cut {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
    (error : Error) (edge : hashv parts = .fail error) :
    Cuts hashv (.read parts k) (.fail error) [⟨parts,.fail error⟩] :=
  .leaf (.readFail parts k error edge)

theorem syscall_div_cut {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
    (edge : hashv parts = .div) :
    Cuts hashv (.read parts k) .div [⟨parts,.div⟩] :=
  .leaf (.readDiv parts k edge)

/-- Pure Rust rejection retains the earlier digest log and skips the suffix. -/
theorem rust_reject_cut {A E B : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : Code (core.result.Result A E)) (error : E) (events : SdkC_Source.Log)
    (head : Cuts hashv code (.ok (.Err error)) events)
    (k : A → Code (core.result.Result B E)) :
    Cuts hashv (CheckpointBytes5Effect.bind code (fun r => match r with
      | .Ok a => k a
      | .Err e => .done (.Err e))) (.ok (.Err error)) events := by
  simpa only [List.append_nil] using
    Cuts.next (k := fun r => match r with
      | .Ok a => k a
      | .Err e => .done (.Err e)) head
      (Cuts.leaf (NGQ_Cuts.Trace.done (core.result.Result.Err error)))

#print axioms scalar_block_cut
#print axioms syscall_fail_cut
#print axioms syscall_div_cut
#print axioms rust_reject_cut
end AspisR1.NHZ_DRIVER
