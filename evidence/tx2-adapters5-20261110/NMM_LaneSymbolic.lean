import NMM_LaneAcceptance
import NMM_PayloadComponents
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneSymbolic
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
abbrev PureOracle := Nat → Array U8 32#usize → core.result.Result Node Unit

def raw (oracle : PureOracle) (p : NLK_LaneInput.Sized) (level : Fin 20) :=
 oracle (level.val+1) (NLK_LaneInput.frontier p level)

def body (oracle : PureOracle) (p : NLK_LaneInput.Sized) :
 core.result.Result NMM_LaneTranscription.Lane NMM_LaneTranscription.PE :=
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => .Err e
 | .Ok f =>
  match oracle 0 (NLK_LaneInput.root p) with
  | .Err _ => .Err .InvalidAccountData
  | .Ok root =>
   (NKP_LaneCompletion.finish f.bump f.master f.lane f.next root NLK_LaneTable.final
    (NKF_LaneTrace.run NLK_LaneTable.empty (NLK_LaneLoop.occupied f.next)
     (raw oracle p) NLK_LaneLoop.levels NLK_LaneLoop.zero)).1

def value (oracle : PureOracle) (bytes : Slice U8) :=
 if h : bytes.val.length=768 then body oracle ⟨bytes,h⟩
 else (.Err .InvalidAccountData : core.result.Result NMM_LaneTranscription.Lane NMM_LaneTranscription.PE)

theorem bad_length (oracle : PureOracle) (bytes : Slice U8) (bad : bytes.val.length ≠ 768) :
 value oracle bytes = .Err .InvalidAccountData := by
 unfold value
 exact dif_neg bad

theorem run_recorded (oracle : PureOracle) (p : NLK_LaneInput.Sized) (next : U64)
 (levels : List (Fin 20)) (before : Frontier) :
 NMM_LaneReplies.run (fun position bytes => ok (oracle position bytes)) p next levels before =
 ok (NKF_LaneTrace.run NLK_LaneTable.empty (NLK_LaneLoop.occupied next) (raw oracle p) levels before) := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
  simp only [NMM_LaneReplies.run,NMM_LaneReplies.one,NKF_LaneTrace.run,raw,bind_tc_ok]
  cases h : NKF_LaneTrace.iteration (NLK_LaneTable.empty level)
   (NLK_LaneLoop.occupied next level) before level (oracle (level.val+1) (NLK_LaneInput.frontier p level)) with
  | mk reply after =>
   simp only [h]
   cases reply with
   | Err e => rfl
   | Ok u => rw [ih];rfl

theorem body_recorded (oracle : PureOracle) (p : NLK_LaneInput.Sized) :
 NMM_LaneReplies.sized (fun position input => ok (oracle position input)) p = ok (body oracle p) := by
 unfold NMM_LaneReplies.sized body
 cases h : NLK_LaneHeader.sourcePrefix p with
 | Err e => rfl
 | Ok f =>
  cases r : oracle 0 (NLK_LaneInput.root p) with
  | Err e => simp only [bind_tc_ok,r]
  | Ok root => simp only [bind_tc_ok,r,run_recorded]

theorem transcription (oracle : PureOracle) (bytes : Slice U8) :
 NMM_LaneReplies.value (fun position input => ok (oracle position input)) bytes = ok (value oracle bytes) := by
 unfold NMM_LaneReplies.value value
 split
 · exact body_recorded oracle _
 · rfl

def fields (oracle : PureOracle) (p : NLK_LaneInput.Sized)
 (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 core.result.Result NMM_LaneScalarSource.Fields NMM_LaneTranscription.PE :=
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => .Err e
 | .Ok f =>
  match oracle 0 (NLK_LaneInput.root p) with
  | .Err _ => .Err .InvalidAccountData
  | .Ok root =>
   NMM_LaneScalarSource.finish byte level word f.bump f.master f.lane f.next root NLK_LaneTable.final
    (NMM_LaneScalarLoop.run NLK_LaneTable.empty (NLK_LaneLoop.occupied f.next)
     (raw oracle p) level word NLK_LaneLoop.levels (NLK_LaneLoop.zero level word))

theorem projection (oracle : PureOracle) (p : NLK_LaneInput.Sized)
 (byte : Fin 32) (level : Fin 20) (word : Fin 8) :
 NMM_LaneScalarSource.mapOut byte level word (body oracle p) = fields oracle p byte level word := by
 unfold body fields
 cases h : NLK_LaneHeader.sourcePrefix p with
 | Err e => rfl
 | Ok f =>
  cases r : oracle 0 (NLK_LaneInput.root p) with
  | Err e => rfl
  | Ok root => rw [NMM_LaneScalarSource.completion_projection,NMM_LaneScalarLoop.loop_projection]

/-- The arbitrary reply model is instantiated with the CLOSED decoder only
in Lean. The Rust harness contains no canonical-word or digest-value assume. -/
theorem closed (bytes : Slice U8) :
 ok (value (fun _ => NLK_LaneDigest.decode) bytes) = NLK_LaneProgram.reference bytes := by
 have functions : (fun (_ : Nat) input => ok (NLK_LaneDigest.decode input)) =
   (fun (_ : Nat) => NLK_LaneDigest.source) := by
  funext position input
  exact (NLK_LaneDigest.child input).symm
 rw [←transcription,functions,NMM_LaneReplies.adopted]

#print bad_length
#print axioms bad_length
#print run_recorded
#print axioms run_recorded
#print body_recorded
#print axioms body_recorded
#print transcription
#print axioms transcription
#print projection
#print axioms projection
#print closed
#print axioms closed
end NMM_LaneSymbolic
