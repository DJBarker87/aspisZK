import R1LiteralByteProtocol

/-! Generic transcript indexing facts for the literal byte-address protocol.
These identify the protocol's own recursive transcript entries; they do not
assert decoder success, acceptance, or source correspondence. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralByteRunFacts

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript

theorem transcript_round (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : LiteralProtocol.Proof) (n : Nat) :
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).round = n :=
  FS2.transcript_round (LiteralByteProtocol.protocol decoder) H pub pf n

theorem transcript_index (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : LiteralProtocol.Proof)
    (n i : Nat) (hi : i < n) :
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds[i]? =
      some (pf i,
        (eval H (LiteralByteSampler.samp i
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i)).toProgram).2) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      let pr := LiteralByteProtocol.protocol decoder
      have hround : (pr.transcript H pub pf n).rounds.length = n := by
        have h := FS2.transcript_round pr H pub pf n
        exact h
      by_cases hlt : i < n
      · change ((pr.transcript H pub pf n).rounds ++
          [(pr.msg pf n, (eval H (pr.samp n (pr.transcript H pub pf n)
            (pr.msg pf n)).toProgram).2)])[i]? = _
        rw [List.getElem?_append_left (by omega : i < (pr.transcript H pub pf n).rounds.length)]
        simpa [pr, LiteralByteProtocol.protocol] using ih i hlt
      · have hieq : i = n := by omega
        subst i
        change ((pr.transcript H pub pf n).rounds ++
          [(pr.msg pf n, (eval H (pr.samp n (pr.transcript H pub pf n)
            (pr.msg pf n)).toProgram).2)])[n]? = _
        rw [List.getElem?_append_right (by rw [hround])]
        rw [hround, Nat.sub_self]
        rfl

#print axioms transcript_round
#print axioms transcript_index

end AspisR1.LiteralByteRunFacts
end
