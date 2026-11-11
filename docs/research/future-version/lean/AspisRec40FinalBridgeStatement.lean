import AspisRows40Protocol
import AspisRows40FinalByte
import RWireLiteralLegacyDecoderCompletion

/-! The byte-to-address bridge for rows 33 to 39 (work order W4), STATED
only: a `def … : Prop`, so nothing is assumed and nothing is proved here.

Copy of R1's `RWireRawLiteralDecoderRestore.decodes_and_follows` (row n < 33,
the public statement given to the decoder) for 33 ≤ n < 40 with the Aspis
decoder `AspisRows40.FinalByte.fin n`, which selects the public statement
itself. Premises: R1's (`hvalid` for rows below 33, `hprior`, `hQ`, `hout`),
the late-row premise on the literal constructor (rows 33 to 39 are
`.payload b`; `FinalShape.LatePayload` is on the erased message, and a
literal `.c2` or `.second` there erases to a payload but breaks the byte-level
restore), and R1's tag premise
`pub.tag = 2` (needed because `fin` selects the statement with the fixed tag 2,
as in `AspisRec40.FinalSelect.select_at` and R1's `select_actual_run`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalBridgeStatement
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1
open CanonicalCutEnrichedTranscript (Words enrichPrefix enrichMessage)

/-- The 40-row raw trace after a prior trace (copy of
`RWireLiteralLegacyDecoderCompletion.rawTrace` with the 40-row protocol). -/
def rawTrace40 (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (prior : List (Bytes × State)) : List (Bytes × State) :=
  prior ++ (eval H (FS2.verifier (AspisRows40.Protocol.protocol decoder) draw pub pf)).1

/-- W4, stated. -/
def DecodesAndFollows40 : Prop :=
  ∀ (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof),
    (∀ i < 33, LiteralTranscript.valid i (pf i)) →
    (∀ i, 33 ≤ i → i < 40 → ∃ b, pf i = .payload b) →
    pub.tag = 2 →
    ∀ (prior : List (Bytes × State)), (∀ q ∈ prior, q.2 = H q.1) →
    ∀ (Q : Nat),
    firstReads emptyTable (rawTrace40 decoder draw H pub pf prior) ≤ Q →
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable (rawTrace40 decoder draw H pub pf prior) →
    ∀ (n : Nat), 33 ≤ n → n < 40 →
    ∀ (raw : Bytes),
    firstCell ((AspisRows40.Protocol.protocol decoder).chain H pub pf n) = some raw →
    ∀ (W : Words),
      let tr := rawTrace40 decoder draw H pub pf prior
      let T := tableBefore emptyTable tr raw
      LiteralTableWordChoiceBin.choose raw T
          (LiteralTranscript.erasePrefix
            ((AspisRows40.Protocol.protocol decoder).transcript H pub pf n))
          (LiteralTranscript.erase (pf n)) = W →
      ∃ own pend g, AspisRows40.FinalByte.fin n raw T = some (own, pend, g) ∧
        bfollow g (traceFrom tr raw) own pend T =
          some (enrichPrefix W ((AspisRows40.Protocol.protocol decoder).transcript H pub pf n),
            enrichMessage W (pf n),
            (AspisRows40.Protocol.protocol decoder).chal H pub pf n)

end AspisRec40.FinalBridgeStatement
end
