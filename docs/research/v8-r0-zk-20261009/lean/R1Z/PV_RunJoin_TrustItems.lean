import R1Z.PV_RunJoin_NativeEffectTransport
import R1Z.PV_RunJoin_E1Joint
import R1Z.ProverCommitPublicNonce40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TrustBoundary
open PV_RunJoin_OsWorld PV_RunJoin_NativeEffectInterface

/-- One tagged call family prevents duplicate trust clauses for dictionary
leaves. Every call retains its complete pre-world and exact returned value. -/
inductive Call (E File Reply Time Worker : Type) where
  | entropy (i : Fin 128) (reply : PV_RunJoin_CallerWorld.RawReply E)
  | file (request : Request File) (reply : Reply) (next : World E File Reply Time Worker)
  | time (outcome : Time) (next : World E File Reply Time Worker)
  | worker (outcome : Worker) (next : World E File Reply Time Worker)

variable {E File Reply Time Worker : Type} [DecidableEq File]

def nativeCall (n : Native E File Reply Time Worker)
    (w : World E File Reply Time Worker) : Call E File Reply Time Worker → Prop
  | .entropy i reply => n.entropyDraw w i reply
  | .file request reply next => fileStep request w = some (reply,next) ∧
      PV_RunJoin_NativeEffectTransport.permitted n w request reply
  | .time outcome next => timeStep w = some (outcome,next) ∧ n.time w outcome
  | .worker outcome next => workerStep w = some (outcome,next) ∧ n.worker w outcome

def sourceCall (l : Laws E File Reply Time Worker)
    (w : World E File Reply Time Worker) : Call E File Reply Time Worker → Prop
  | .entropy i reply => EntropyAllowed l w i reply
  | .file request reply next => FileAllowed l w request reply next
  | .time outcome next => TimeAllowed l w outcome next
  | .worker outcome next => WorkerAllowed l w outcome next

/-- Data still requiring the actual deployment interpretation. Observation
must retain BOTH the filesystem state/effects and the complete D159 observer;
no simulator or security-experiment agreement occurs in this signature. -/
structure Data (E File Reply Time Worker Context Coins Rest Observation : Type) where
  native : Native E File Reply Time Worker
  laws : Laws E File Reply Time Worker
  law : Context → ProverCommitPublicNonce40.Raw → ℚ
  frame : Fin 128 → (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest → Context
  coordinates : Coins ≃ (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest
  nativeWeight : Coins → ℚ
  nativeObservation : Coins → Observation
  extractedObservation : Coins → Observation

end R1Z.PV_RunJoin_TrustBoundary
namespace R1Z
open PV_RunJoin_TrustBoundary
variable {E File Reply Time Worker Context Coins Rest Observation : Type}
variable [DecidableEq File] [Fintype Rest]

/-- Proposed native trust list, NOT an installed deployment certificate.
P obligations (selection, admission, extracted trace simulation, release
identity) are deliberately absent. See the stage report for code locations
and the consequence of each field failing. -/
structure PV_RunJoin_TrustItems
    (d : Data E File Reply Time Worker Context Coins Rest Observation) : Prop where
  /-- OS/kernel contract: successful 64-byte getrandom conditional law. -/
  entropy_law : ProverCommitPublicNonce40.E1 d.law
  /-- OS/kernel contract: actual joint density, not just uniform marginals. -/
  entropy_kernel : ∀ c, d.nativeWeight c =
    PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c
  /-- OS/kernel contract: getrandom, open64/read/write/sync/close, time,
  and workers on the same world. No availability assertion. -/
  outcomes : ∀ w call, nativeCall d.native w call ↔ sourceCall d.laws w call
  /-- OS/kernel + toolchain + hardware: native filesystem/E2 and complete
  observation match extracted execution, including error and side channels.
  This does NOT assert extracted-execution/security-experiment agreement. -/
  observation : ∀ c, d.nativeObservation c = d.extractedObservation c

#print PV_RunJoin_TrustItems
end R1Z
