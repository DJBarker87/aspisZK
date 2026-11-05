import NIA_DriverPackets
import NHZ_CheckpointEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIC_AbortPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- A stopped primitive is an abort-prefix edge, not a Rust Err reply.
The continuation is universally quantified and is never evaluated. -/
theorem read_fail {A C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (parts : SdkC_Source.Parts) (error : Error)
 (edge : hashv parts = .fail error) (suffix : SdkC_Source.Digest → Code A)
 (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (.read parts suffix) prior)=
 (context,(.fail error,prior++[⟨parts,.fail error⟩])) := by
 have t : NGQ_Cuts.Trace hashv (.read parts suffix) (.fail error)
   [⟨parts,.fail error⟩] := .readFail _ _ error edge
 rw [NGQ_Cuts.run t prior]

theorem read_div {A C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (parts : SdkC_Source.Parts)
 (edge : hashv parts = .div) (suffix : SdkC_Source.Digest → Code A)
 (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (.read parts suffix) prior)=
 (context,(.div,prior++[⟨parts,.div⟩])) := by
 have t : NGQ_Cuts.Trace hashv (.read parts suffix) .div
   [⟨parts,.div⟩] := .readDiv _ _ edge
 rw [NGQ_Cuts.run t prior]

/-- Allocation is erased by the emitted constructor endpoint. This explicit
partial allocation step records the retained allocator abort semantics; no
recoverable verifier::Error::Allocation arm is introduced for Box::new. -/
theorem allocation_div {A B C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (suffix : B → Code A) (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (.step (.div : Result B) suffix) prior)=
 (context,(.div,prior)) := by
 have t : NGQ_Cuts.Trace hashv (.step (.div : Result B) suffix) .div [] :=
   .stepDiv _ _ rfl
 simpa only [List.append_nil] using congrArg (fun r => (context,r)) (NGQ_Cuts.run t prior)

/-- SAME scalar prestate and packet as NIA, lifted to an arbitrary context.
The native abort edge's interpretation still uses RuntimeSyscall, not totality. -/
theorem scalar_stopped {C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (B : AspisR1PublicPreparation.PreparedModel.Boundaries) (mode : Bool)
 (before : AspisR1PublicPreparation.transcript.Transcript Unit)
 (row : U8) (payload : Slice U8) (stop : NIA_ScalarFailures.Stop)
 (events : SdkC_Source.Log)
 (packet : NIA_ScalarFailures.BlockStop hashv before row payload stop events)
 (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (NIA_ScalarEffects.scalarCode B before row payload mode) prior)=
 (context,(stop.result,prior++events)) ∧
 (context,SdkC_Source.run hashv (NIA_ScalarEffects.scalarKCode B before row payload) prior)=
 (context,(stop.result,prior++events)) := by
 obtain ⟨scalar,scalarK⟩ := NIA_ScalarFailures.frame B mode packet prior
 exact ⟨congrArg (fun r => (context,r)) scalar,congrArg (fun r => (context,r)) scalarK⟩

#print axioms read_fail
#print axioms read_div
#print axioms allocation_div
#print axioms scalar_stopped
end AspisR1.NIC_AbortPrefix
