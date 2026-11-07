import NMM_LaneTranscription
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneReplies
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
abbrev Oracle := Nat → Array U8 32#usize → Result (core.result.Result Node Unit)

def one (oracle : Oracle) (p : NLK_LaneInput.Sized) (next : U64)
 (before : Frontier) (level : Fin 20) : Result (Reply × Frontier) := do
 let raw ← oracle (level.val+1) (NLK_LaneInput.frontier p level)
 ok (NKF_LaneTrace.iteration (NLK_LaneTable.empty level)
   (NLK_LaneLoop.occupied next level) before level raw)

def run (oracle : Oracle) (p : NLK_LaneInput.Sized) (next : U64) :
 List (Fin 20) → Frontier → Result (Reply × Frontier × List (Fin 20))
 | [], before => ok (.Ok (), before, [])
 | level::rest, before => do
  let current ← one oracle p next before level
  match current.1 with
  | .Err e => ok (.Err e,current.2,[level])
  | .Ok _ =>
   let tail ← run oracle p next rest current.2
   ok (tail.1,tail.2.1,level::tail.2.2)

def sized (oracle : Oracle) (p : NLK_LaneInput.Sized) :
 Result (core.result.Result NMM_LaneTranscription.Lane NMM_LaneTranscription.PE) := do
 match NLK_LaneHeader.sourcePrefix p with
 | .Err e => ok (.Err e)
 | .Ok f =>
  let raw ← oracle 0 (NLK_LaneInput.root p)
  match raw with
  | .Err _ => ok (.Err .InvalidAccountData)
  | .Ok root =>
   let loop ← run oracle p f.next NLK_LaneLoop.levels NLK_LaneLoop.zero
   ok (NKP_LaneCompletion.finish f.bump f.master f.lane f.next root
    NLK_LaneTable.final loop).1

def value (oracle : Oracle) (bytes : Slice U8) :=
 if h : bytes.val.length=768 then sized oracle ⟨bytes,h⟩
 else ok (.Err .InvalidAccountData)

theorem run_closed (p : NLK_LaneInput.Sized) (next : U64)
 (levels : List (Fin 20)) (before : Frontier) :
 run (fun _ => NLK_LaneDigest.source) p next levels before =
 NLK_LaneLoopSource.run p next levels before := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
  simp only [run,one,NLK_LaneLoopSource.run,NLK_LaneLoopSource.one]
  congr 1
  funext current
  cases current with
  | mk reply after =>
   cases reply with
   | Err e => rfl
   | Ok u => rw [ih]

theorem closed (bytes : Slice U8) :
 value (fun _ => NLK_LaneDigest.source) bytes=NMM_LaneTranscription.value bytes := by
 unfold value NMM_LaneTranscription.value
 split
 · simp only [sized,NMM_LaneTranscription.sized,run_closed]
   rfl
 · rfl

theorem adopted (bytes : Slice U8) :
 value (fun _ => NLK_LaneDigest.source) bytes=NLK_LaneProgram.reference bytes := by
 rw [closed,NMM_LaneTranscription.adopted_value]

#print run_closed
#print axioms run_closed
#print closed
#print axioms closed
#print adopted
#print axioms adopted
end NMM_LaneReplies
