import R1UnifiedVerifier

/-! Replacing an unobserved row-zero payload by any fixed message leaves the
unified transcript and verifier program unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPayloadZero

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

def payload (m0 : M) (f : Nat → M) (n : Nat) : M :=
  if n = 0 then m0 else f n

def proof (m0 : M) (π : AspisR1.UnifiedProtocol.Proof M) :
    AspisR1.UnifiedProtocol.Proof M := (π.1, payload m0 π.2)

theorem payload_zero (m0 : M) (f : Nat → M) : payload m0 f 0 = m0 := by
  simp [payload]

theorem payload_ne_zero (m0 : M) (f : Nat → M) {n : Nat} (hn : n ≠ 0) :
    payload m0 f n = f n := by
  simp [payload, hn]

theorem message_eq (c1 : State) (m0 : M) (f : Nat → M) :
    ∀ n, AspisR1.UnifiedRun.message c1 (payload m0 f) n =
      AspisR1.UnifiedRun.message c1 f n := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem transcript_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : AspisR1.UnifiedSampler.Public L)
    (c1 : State) (m0 : M) (f : Nat → M) : ∀ n,
    AspisR1.UnifiedRun.transcript p hD H pub c1 (payload m0 f) n =
      AspisR1.UnifiedRun.transcript p hD H pub c1 f n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [AspisR1.UnifiedRun.transcript_succ, AspisR1.UnifiedRun.transcript_succ, ih]
      have hm := message_eq c1 m0 f n
      have hc : AspisR1.UnifiedRun.challenge p hD H pub c1 (payload m0 f) n =
          AspisR1.UnifiedRun.challenge p hD H pub c1 f n := by
        unfold AspisR1.UnifiedRun.challenge
        rw [ih, hm]
      rw [hm, hc]

theorem challenge_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : AspisR1.UnifiedSampler.Public L)
    (c1 : State) (m0 : M) (f : Nat → M) (n : Nat) :
    AspisR1.UnifiedRun.challenge p hD H pub c1 (payload m0 f) n =
      AspisR1.UnifiedRun.challenge p hD H pub c1 f n := by
  unfold AspisR1.UnifiedRun.challenge
  rw [transcript_eq, message_eq]

theorem state_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : AspisR1.UnifiedSampler.Public L)
    (c1 : State) (m0 : M) (f : Nat → M) (n : Nat) :
    AspisR1.UnifiedRun.state p hD H pub c1 (payload m0 f) n =
      AspisR1.UnifiedRun.state p hD H pub c1 f n := by
  unfold AspisR1.UnifiedRun.state
  rw [transcript_eq]

theorem protocol_message_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (π : UnifiedProtocol.Proof M) (m0 : M) (i : Nat) :
    (UnifiedProtocol.protocol p hD extract).msg (proof m0 π) i =
      (UnifiedProtocol.protocol p hD extract).msg π i := by
  exact message_eq π.1 m0 π.2 i

theorem protocol_transcript_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (m0 : M) (n : Nat) :
    (UnifiedProtocol.protocol p hD extract).transcript H pub (proof m0 π) n =
      (UnifiedProtocol.protocol p hD extract).transcript H pub π n := by
  rw [UnifiedProtocol.transcript_eq p hD extract H pub (proof m0 π) n,
    UnifiedProtocol.transcript_eq p hD extract H pub π n]
  exact transcript_eq p hD H pub π.1 m0 π.2 n

theorem protocol_chain_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (m0 : M) (i : Nat) :
    (UnifiedProtocol.protocol p hD extract).chain H pub (proof m0 π) i =
      (UnifiedProtocol.protocol p hD extract).chain H pub π i := by
  rw [UnifiedProtocol.chain_eq p hD extract H pub (proof m0 π) i,
    UnifiedProtocol.chain_eq p hD extract H pub π i]
  rw [transcript_eq, message_eq]

theorem protocol_challenge_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (m0 : M) (i : Nat) :
    (UnifiedProtocol.protocol p hD extract).chal H pub (proof m0 π) i =
      (UnifiedProtocol.protocol p hD extract).chal H pub π i := by
  rw [UnifiedProtocol.chal_eq p hD extract H pub (proof m0 π) i,
    UnifiedProtocol.chal_eq p hD extract H pub π i]
  rw [transcript_eq, message_eq]

private theorem verifierFrom_msg_congr {X M C W Pf I A : Type}
    [DecidableEq I] [Inhabited A]
    (pr : FS2.Protocol X M C W Pf I A)
    (decision : FS.Prefix X M C → M → Bool) (π π' : Pf)
    (hm : ∀ i, pr.msg π i = pr.msg π' i) : ∀ n P,
      FS2.verifierFrom pr decision π n P = FS2.verifierFrom pr decision π' n P := by
  intro n
  induction n with
  | zero =>
      intro P
      simp [FS2.verifierFrom, hm]
  | succ n ih =>
      intro P
      simp only [FS2.verifierFrom]
      rw [hm (pr.r - (n + 1))]
      congr 1
      funext c
      exact ih (P.ext (pr.msg π' (pr.r - (n + 1))) c)

theorem verifier_eq {W : Type} (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : AspisR1.UnifiedSampler.Public L →
      Table (Addr L) State → Option W)
    (decision : FS.Prefix (AspisR1.UnifiedSampler.Public L)
      (AspisR1.TranscriptView.Message M) (AspisR1.TranscriptView.Challenge Cv) →
      AspisR1.TranscriptView.Message M → Bool)
    (pub : AspisR1.UnifiedSampler.Public L) (π : AspisR1.UnifiedProtocol.Proof M)
    (m0 : M) :
    AspisR1.UnifiedVerifier.verifier p hD extract decision pub (proof m0 π) =
      AspisR1.UnifiedVerifier.verifier p hD extract decision pub π := by
  unfold AspisR1.UnifiedVerifier.verifier FS2.verifier
  apply verifierFrom_msg_congr
  intro i
  exact message_eq π.1 m0 π.2 i

#print axioms payload_zero
#print axioms payload_ne_zero
#print axioms message_eq
#print axioms transcript_eq
#print axioms challenge_eq
#print axioms state_eq
#print axioms protocol_message_eq
#print axioms protocol_transcript_eq
#print axioms protocol_chain_eq
#print axioms protocol_challenge_eq
#print axioms verifier_eq

end AspisR1.UnifiedPayloadZero
end
