import R1UnifiedSampler

/-! A deterministic oracle run of the unified sampler schedule, represented
as an ordinary FS prefix. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRun

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

def message (c1 : State) (payload : Nat → M) : Nat → Message M
  | 0 => .initial c1
  | i + 1 => .payload (payload (i + 1))

def transcript (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : Nat → UnifiedSampler.Prefix M Cv L
  | 0 => FS.emptyPrefix pub
  | n + 1 =>
      let P := transcript p hD H pub c1 payload n
      P.ext (message c1 payload n)
        (eval H (UnifiedSampler.samp p hD n P (message c1 payload n)).toProgram).2

def challenge (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat) : Challenge Cv :=
  (eval H (UnifiedSampler.samp p hD n
    (transcript p hD H pub c1 payload n)
    (message c1 payload n)).toProgram).2

def state (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat) : State :=
  UnifiedSampler.stateOf p (transcript p hD H pub c1 payload n)

theorem transcript_succ (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat) :
    transcript p hD H pub c1 payload (n + 1) =
      (transcript p hD H pub c1 payload n).ext
        (message c1 payload n) (challenge p hD H pub c1 payload n) := rfl

theorem transcript_statement (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : ∀ n,
    (transcript p hD H pub c1 payload n).statement = pub := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [transcript, FS.Prefix.ext, ih]

theorem transcript_length (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : ∀ n,
    (transcript p hD H pub c1 payload n).rounds.length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [transcript, FS.Prefix.ext, ih]

theorem state_succ (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat) :
    state p hD H pub c1 payload (n + 1) = (challenge p hD H pub c1 payload n).2 := by
  unfold state
  rw [transcript_succ]
  exact UnifiedSampler.stateOf_ext p
    (transcript p hD H pub c1 payload n) (message c1 payload n)
    (challenge p hD H pub c1 payload n)

theorem transcript_rounds (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : ∀ n,
    (transcript p hD H pub c1 payload n).rounds =
      (List.range n).map (fun j =>
        (message c1 payload j, challenge p hD H pub c1 payload j)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [transcript_succ]
      simp [FS.Prefix.ext, List.range_succ, List.map_append, ih]

#print axioms transcript_succ
#print axioms transcript_statement
#print axioms transcript_length
#print axioms state_succ
#print axioms transcript_rounds

end AspisR1.UnifiedRun
end
