import R1LiteralByteProtocol
import R1UnifiedProtocol

/-! An explicit legacy proof tuple for each well-shaped literal proof.
Its erased transcript and sampler executions are exactly the old unified
33-row protocol. Literal word metadata is retained by the literal protocol;
this module only identifies its byte-level sampler with the old decoder's
input carrier. No source acceptance or decoder-completion premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralLegacyRun

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev L := SelectedTranscriptParams.L
abbrev BytesMessage := LiteralTranscript.BytesMessage
abbrev Proof := LiteralProtocol.Proof

def bytesOf : LiteralTranscript.Message → BytesMessage
  | .initial _ _ => ⟨[], by simp [SelectedTranscriptParams.D]⟩
  | .payload b => b
  | .c2 b _ => b
  | .second b _ => b

def root (pf : Proof) : State :=
  match pf 0 with
  | .initial r _ => r
  | _ => default

def proof (pf : Proof) : UnifiedProtocol.Proof BytesMessage :=
  (root pf, fun i => bytesOf (pf i))

def legacyProtocol := UnifiedProtocol.protocol SelectedTranscriptParams.params
  (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
  (fun _ _ => (none : Option Unit))

theorem message_eq (pf : Proof) (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (i : Nat) (hi : i < 33) :
    LiteralTranscript.erase (pf i) = legacyProtocol.msg (proof pf) i := by
  have hv := hvalid i hi
  cases i with
  | zero =>
      cases hp : pf 0 <;>
        simp_all [LiteralTranscript.valid, LiteralTranscript.erase,
          legacyProtocol, UnifiedProtocol.protocol, UnifiedRun.message, proof, root]
  | succ i =>
      cases hp : pf (i+1) with
      | initial r w =>
          simp [hp, LiteralTranscript.valid] at hv
      | payload b => simp [legacyProtocol, UnifiedProtocol.protocol, UnifiedRun.message, proof, bytesOf, LiteralTranscript.erase, hp]
      | c2 b w => simp [legacyProtocol, UnifiedProtocol.protocol, UnifiedRun.message, proof, bytesOf, LiteralTranscript.erase, hp]
      | second b w => simp [legacyProtocol, UnifiedProtocol.protocol, UnifiedRun.message, proof, bytesOf, LiteralTranscript.erase, hp]

theorem erased_run_eq (H : Addr L → State) (pub : LiteralTranscript.Public)
    (pf : Proof) (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (n : Nat) (hn : n ≤ 33) :
    LiteralRun.erasedTranscript H pub pf n =
      legacyProtocol.transcript H pub (proof pf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hi : n < 33 := by omega
      have he := message_eq pf hvalid n hi
      change (LiteralRun.erasedTranscript H pub pf n).ext (LiteralTranscript.erase (pf n))
          (eval H (UnifiedSampler.samp SelectedTranscriptParams.params _ n
            (LiteralRun.erasedTranscript H pub pf n) (LiteralTranscript.erase (pf n))).toProgram).2 =
        (legacyProtocol.transcript H pub (proof pf) n).ext
          (legacyProtocol.msg (proof pf) n)
          (eval H (legacyProtocol.samp n
            (legacyProtocol.transcript H pub (proof pf) n)
            (legacyProtocol.msg (proof pf) n)).toProgram).2
      rw [ih (by omega), he]
      rfl

theorem erased_transcript_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (n : Nat) (hn : n ≤ 33) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) =
      legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change LiteralTranscript.erasePrefix
        (((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext (pf n)
          (eval H (LiteralByteSampler.samp n
            ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n)).toProgram).2) = _
      rw [LiteralTranscript.erasePrefix_ext, LiteralByteSampler.eval_eq]
      change (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).ext
        (LiteralTranscript.erase (pf n))
        (eval (fun a => H a.toBytes) (UnifiedSampler.samp SelectedTranscriptParams.params _ n
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
          (LiteralTranscript.erase (pf n))).toProgram).2 =
        (legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n).ext
          (legacyProtocol.msg (proof pf) n)
          (eval (fun a => H a.toBytes) (legacyProtocol.samp n
            (legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n)
            (legacyProtocol.msg (proof pf) n)).toProgram).2
      rw [ih (by omega), message_eq pf hvalid n (by omega)]
      rfl

theorem chain_eval_eq (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i))
    (i : Nat) (hi : i < 33) :
    eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram =
      mapView Addr.toBytes
        (eval (fun a => H a.toBytes)
          (legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i).toProgram) := by
  change eval H (LiteralByteSampler.samp i
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i)).toProgram = _
  rw [LiteralByteSampler.eval_eq]
  unfold LiteralTranscript.samp
  rw [erased_transcript_eq decoder H pub pf hvalid i (by omega), message_eq pf hvalid i hi]
  rfl

#print axioms message_eq
#print axioms erased_run_eq
#print axioms erased_transcript_eq
#print axioms chain_eval_eq
end AspisR1.LiteralLegacyRun
end
