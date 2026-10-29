import PV_DIAG3_Observer
/-! Named client diagnostic pieces for PV_RJ4IDB_DiagAdapter.diagTrace.
No observation decoder is defined here. ordered events and terminal are the
existing PV_DIAG3 types, directly consumable by that adapter. Retained state
is preserved in Execution; count is the already public L1 coordinate. -/
set_option autoImplicit false
namespace PV_DIAG5
open PV_DIAG3
variable {S A O : Type}
structure ClientOutput (S A : Type) where
 attemptCount : Nat
 execution : Execution S A
def clientEvents (x : ClientOutput S A) := x.execution.events
def clientTerminal (x : ClientOutput S A) := x.execution.exit
def clientFrames (x : ClientOutput S A) := selectedFrames (clientEvents x)
def clientDelivered (x : ClientOutput S A) := deliveredBytes (clientEvents x)
def clientRequested (x : ClientOutput S A) := requestedBytes (clientEvents x)
def clientPieces (x : ClientOutput S A) := (x.attemptCount,clientEvents x,clientTerminal x)
def prependClient (es : List Event) (x : ClientOutput S A) : ClientOutput S A :=
 ⟨x.attemptCount,prepend es x.execution⟩
theorem output_from_joint_count_execution (rel : S → S → Prop)
 (a b : ClientOutput S A) (hc : a.attemptCount = b.attemptCount)
 (h : Coupled rel a.execution b.execution) : clientPieces a = clientPieces b := by
 unfold clientPieces clientEvents clientTerminal
 rw [hc,h.1,h.2.2]
#print axioms output_from_joint_count_execution
theorem output_retains_prefix (es : List Event) (x : ClientOutput S A) :
 clientEvents (prependClient es x) = es ++ clientEvents x := rfl
#print axioms output_retains_prefix
theorem prefix_keeps_terminal (es : List Event) (x : ClientOutput S A) :
 clientTerminal (prependClient es x) = clientTerminal x := rfl
#print axioms prefix_keeps_terminal
theorem pieces_determine_events (x y : ClientOutput S A) (h : clientPieces x = clientPieces y) :
 clientEvents x = clientEvents y := congrArg (fun p => p.2.1) h
#print axioms pieces_determine_events
theorem pieces_determine_frames (x y : ClientOutput S A) (h : clientPieces x = clientPieces y) :
 clientFrames x = clientFrames y := congrArg selectedFrames (pieces_determine_events x y h)
#print axioms pieces_determine_frames
theorem pieces_determine_delivery (x y : ClientOutput S A) (h : clientPieces x = clientPieces y) :
 clientDelivered x = clientDelivered y := congrArg deliveredBytes (pieces_determine_events x y h)
#print axioms pieces_determine_delivery
theorem external_decoder_transport (decode : Execution S A → O)
 (decision : O → Bool) (x y : ClientOutput S A)
 (nativeDecoderAssociation : decode x.execution = decode y.execution) :
 (decode x.execution,decision (decode x.execution)) =
 (decode y.execution,decision (decode y.execution)) := by rw [nativeDecoderAssociation]
#print axioms external_decoder_transport
theorem result_only_recovery_obligation {R : Type}
 (recover : R → List Event) (result : R) (a b : ClientOutput S A)
 (ha : recover result = clientEvents a) (hb : recover result = clientEvents b) :
 clientEvents a = clientEvents b := ha.symm.trans hb
#print axioms result_only_recovery_obligation
end PV_DIAG5
