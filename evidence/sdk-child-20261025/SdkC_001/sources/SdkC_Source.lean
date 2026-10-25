import S2W_DigestExtraction
import CheckpointBytes5Effect
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Source
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
abbrev Parts := S2Z.Oracle.Parts
abbrev Digest := S2Z.Oracle.Digest
abbrev Code := CheckpointBytes5Effect.Code

/-- Every attempted syscall is retained, even on failure or divergence. -/
structure Query where
  parts : Parts
  returned : Result Digest
abbrev Log := List Query

def readLog (log : Log) : List (Bytes × State) := log.filterMap fun q =>
  match q.returned with
  | .ok digest => some (flatten q.parts, decodeState digest)
  | _ => none

/-- Evaluate the literal effect syntax with the real partial syscall.
No successful trace, erased child, or total-oracle port is an input. -/
def run (hashv : Parts → Result Digest) {A : Type} : Code A → Log → Result A × Log
  | .done a, log => (.ok a,log)
  | .step r k, log => match r with
    | .ok a => run hashv (k a) log
    | .fail e => (.fail e,log)
    | .div => (.div,log)
  | .read parts k, log =>
    let answer := hashv parts
    let next := log ++ [⟨parts,answer⟩]
    match answer with
    | .ok digest => run hashv (k digest) next
    | .fail e => (.fail e,next)
    | .div => (.div,next)

/-- Exact digest dictionary used to erase source effect syntax. -/
def dictionary (hashv : Parts → Result Digest) :
    AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst := {}, digest := fun _ parts => hashv parts}

theorem erasure (hashv : Parts → Result Digest) {A : Type}
    (code : Code A) (before : Log) :
    (run hashv code before).1 = CheckpointBytes5Effect.erase (dictionary hashv) () code := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih => cases r <;> simp only [run,CheckpointBytes5Effect.erase,bind_tc_ok,
      bind_tc_fail,bind_tc_div] <;> first | rfl | apply ih
  | read parts k ih =>
    cases h : hashv parts <;>
      simp only [run,h,CheckpointBytes5Effect.erase,dictionary,bind_tc_ok,bind_tc_fail,bind_tc_div]
    all_goals first | rfl | apply ih

theorem extends (hashv : Parts → Result Digest) {A : Type}
    (code : Code A) (before : Log) :
    ∃ suffix, (run hashv code before).2 = before ++ suffix := by
  induction code generalizing before with
  | done a => exact ⟨[],(List.append_nil _).symm⟩
  | step r k ih =>
    cases r with
    | fail e => exact ⟨[],(List.append_nil _).symm⟩
    | div => exact ⟨[],(List.append_nil _).symm⟩
    | ok a => exact ih a before
  | read parts k ih =>
    cases h : hashv parts with
    | fail e => exact ⟨[⟨parts,.fail e⟩],by simp only [run,h]⟩
    | div => exact ⟨[⟨parts,.div⟩],by simp only [run,h]⟩
    | ok digest =>
      obtain ⟨suffix,eq⟩ := ih digest (before ++ [⟨parts,.ok digest⟩])
      exact ⟨⟨parts,.ok digest⟩ :: suffix, by simpa only [run,h,List.append_assoc,
        List.singleton_append] using eq⟩

/-- All newly recorded attempts are the actual syscall's result at that input. -/
theorem associated (hashv : Parts → Result Digest) {A : Type}
    (code : Code A) (before : Log)
    (initial : ∀ q ∈ before, q.returned = hashv q.parts) :
    ∀ q ∈ (run hashv code before).2, q.returned = hashv q.parts := by
  induction code generalizing before with
  | done a => exact initial
  | step r k ih => cases r with
    | ok a => exact ih a before initial
    | fail e => exact initial
    | div => exact initial
  | read parts k ih =>
    have next : ∀ q ∈ before ++ [⟨parts,hashv parts⟩], q.returned = hashv q.parts := by
      intro q member
      rcases List.mem_append.mp member with old | fresh
      · exact initial q old
      · obtain rfl := List.mem_singleton.mp fresh
        rfl
    cases h : hashv parts with
    | ok digest => simpa only [run,h] using ih digest (before ++ [⟨parts,.ok digest⟩])
        (by simpa only [h] using next)
    | fail e => simpa only [run,h] using next
    | div => simpa only [run,h] using next

/-- Success-conditioned ROM interpretation; no syscall totality is assumed. -/
theorem consistent (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) :
    ∀ q ∈ readLog (run hashv code []).2, q.2 = H q.1 := by
  intro q member
  obtain ⟨attempt,belongs,emitted⟩ := List.mem_filterMap.mp member
  have actual := associated hashv code [] (by simp) attempt belongs
  cases returned : attempt.returned with
  | fail e => simp only [readLog] at member; simp [returned] at emitted
  | div => simp [returned] at emitted
  | ok digest =>
    simp only [returned,Option.some.injEq] at emitted
    subst q
    exact (syscall.returningValue attempt.parts digest (returned.symm.trans actual).symm).trans
      (p1.realization _)

/-- The literal shipped digest wrapper: one hashv, followed by pure toBytes. -/
def digestCode (parts : Parts) : Code Digest :=
  .read parts (fun digest => .step (S2W_DigestExtraction.toBytes digest) .done)

theorem digest_erasure (hashv : Parts → Result Digest)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    (run hashv (digestCode parts) []).1 = S2W_DigestExtraction.digest hashv self parts := by
  rw [S2W_DigestExtraction.digest_eq_hashv]
  cases h : hashv parts <;> simp [run,digestCode,h,S2W_DigestExtraction.toBytes]

theorem digest_trace (hashv : Parts → Result Digest) (parts : Parts) (before : Log) :
    run hashv (digestCode parts) before = (hashv parts,before ++ [⟨parts,hashv parts⟩]) := by
  cases h : hashv parts <;> simp [run,digestCode,h,S2W_DigestExtraction.toBytes]

/-- D188 supplies the same actual op43 result, not a new source assumption. -/
theorem installed_digest (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    (run hashv (digestCode parts) []).1 = ops.op43 self parts :=
  (digest_erasure hashv self parts).trans (extraction.digestSource self parts).symm

#print axioms erasure
#print axioms extends
#print axioms associated
#print axioms consistent
#print axioms digest_erasure
#print axioms digest_trace
#print axioms installed_digest
end AspisR1.SdkC_Source
end
