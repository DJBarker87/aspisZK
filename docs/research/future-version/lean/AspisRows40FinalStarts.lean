import AspisRows40Starts
import AspisRows40FinalByte

/-! Aspis one-transaction verifier: the decoded-start counts with the concrete
final component (`FinalByte.fin`) in place of the parameter.

* `verifier_starts`: the 40-row verifier has at most 41 decoded first reads
  under the concrete Aspis byte decoder `decFinal`.
* `final_row_starts`: row n (33 ≤ n < 40) has exactly
  `[T a = none ∧ fin n a T ≠ none]` decoded first reads, `a` its absorb frame.
* `final_row_one`: that count is 1 when the frame is FRESH (`T a = none`: the
  incoming table, i.e. every oracle call before this row's absorb in the
  experiment, has not read this exact byte string) and the decoder succeeds
  there; `final_row_one_of_parse` reduces success to the statement selection
  and the context parse at the bounded table; `row33_one` reduces row 33's
  success further to R1's row-32 objects (the advance/absorb walk from the
  state after row 32, R1's `JointContext.parse` with 31 records, and R1's
  `FullPublicSelection.select` at row 32's frame). -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.FinalStarts
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1
open DecodedFirstReadUnionBound BinHonestQueryBudget
open AspisPerStep.WeightedFirstRead

/-- The concrete Aspis byte decoder. -/
def decFinal : Starts.BDec := Starts.decAspis FinalByte.fin

theorem verifier_starts (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstReads decFinal T (eval H (Starts.verifier D d pub pf)).1 ≤ 41 :=
  Starts.verifier_starts FinalByte.fin D d H pub pf T

theorem final_row_starts (H : Addr BinHonestStartFrames.L → State) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E BinHonestStartFrames.L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State) :
    let a := (UnifiedSampler.absorb BinHonestStartFrames.p n P msg).toBytes
    decoderFirstReads decFinal T (raw (eval H (UnifiedSampler.samp BinHonestStartFrames.p
      (by norm_num [BinHonestStartFrames.p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        n P (.payload msg)).toProgram).1) =
      (if T a = none ∧ FinalByte.fin n a T ≠ none then 1 else 0) :=
  Starts.final_row_starts FinalByte.fin H n hlo hhi P msg T

theorem final_row_one (H : Addr BinHonestStartFrames.L → State) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E BinHonestStartFrames.L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State)
    (hfresh : T (UnifiedSampler.absorb BinHonestStartFrames.p n P msg).toBytes = none)
    (hok : FinalByte.fin n (UnifiedSampler.absorb BinHonestStartFrames.p n P msg).toBytes T ≠ none) :
    decoderFirstReads decFinal T (raw (eval H (UnifiedSampler.samp BinHonestStartFrames.p
      (by norm_num [BinHonestStartFrames.p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        n P (.payload msg)).toProgram).1) = 1 := by
  rw [final_row_starts H n hlo hhi P msg T]
  exact if_pos ⟨hfresh, hok⟩

theorem final_row_one_of_parse (H : Addr BinHonestStartFrames.L → State) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E BinHonestStartFrames.L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State)
    (pub : UnifiedSampler.Public BinHonestStartFrames.L)
    (ctx : Context.Context SelectedTranscriptParams.Message BinHonestStartFrames.L)
    (hfresh : T (UnifiedSampler.absorb BinHonestStartFrames.p n P msg).toBytes = none)
    (hs : FinalByte.select n (UnifiedSampler.absorb BinHonestStartFrames.p n P msg)
      (RawBoundedTrace.table BinHonestStartFrames.L T) = some pub)
    (hp : Context.parse BinHonestStartFrames.p pub.pubBytes pub.tag n (UnifiedSampler.absorb BinHonestStartFrames.p n P msg)
      (RawBoundedTrace.table BinHonestStartFrames.L T) = some ctx) :
    decoderFirstReads decFinal T (raw (eval H (UnifiedSampler.samp BinHonestStartFrames.p
      (by norm_num [BinHonestStartFrames.p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        n P (.payload msg)).toProgram).1) = 1 :=
  final_row_one H n hlo hhi P msg T hfresh
    (FinalByte.fin_isSome n _ T pub ctx
      (by unfold UnifiedSampler.absorb absorbA; exact CanonicalByteAddress.canonical_ofBytes _ _) hs hp)

/-- Row 33 from R1's row-32 objects at the bounded table `T' = table T`:
the walk from the state `x` after row 32 finds row 32's absorb frame `a32`
(`DuplexSeek.seek` with fuel 2), R1's row-32 context parses there with 31
records, and R1's public selector selects `pub` there. -/
theorem row33_one (H : Addr BinHonestStartFrames.L → State)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E BinHonestStartFrames.L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State)
    (pub : UnifiedSampler.Public BinHonestStartFrames.L) (a32 : Addr BinHonestStartFrames.L) (xs : List State)
    (jc : JointContext.Context SelectedTranscriptParams.Message BinHonestStartFrames.L)
    (hfresh : T (UnifiedSampler.absorb BinHonestStartFrames.p 33 P msg).toBytes = none)
    (hseek : DuplexSeek.seek BinHonestStartFrames.p (RawBoundedTrace.table BinHonestStartFrames.L T) 2
      (UnifiedSampler.stateOf BinHonestStartFrames.p P) = some (a32, xs))
    (hjoint : JointContext.parse BinHonestStartFrames.p pub.pubBytes pub.tag 27 4 a32
      (RawBoundedTrace.table BinHonestStartFrames.L T) = some jc)
    (hlen : jc.records.length = 31)
    (hsel : FullPublicSelection.select BinHonestStartFrames.p a32 (RawBoundedTrace.table BinHonestStartFrames.L T) = some pub) :
    decoderFirstReads decFinal T (raw (eval H (UnifiedSampler.samp BinHonestStartFrames.p
      (by norm_num [BinHonestStartFrames.p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        33 P (.payload msg)).toProgram).1) = 1 := by
  have hp := Context.parse_row33 BinHonestStartFrames.p pub.pubBytes pub.tag (RawBoundedTrace.table BinHonestStartFrames.L T)
    (UnifiedSampler.stateOf BinHonestStartFrames.p P) msg a32 xs jc hseek hjoint hlen
  have hs : FinalByte.select 33 (UnifiedSampler.absorb BinHonestStartFrames.p 33 P msg)
      (RawBoundedTrace.table BinHonestStartFrames.L T) = some pub := by
    unfold FinalByte.select UnifiedSampler.absorb
    rw [parseAbsorb_absorbA, Option.bind_some]
    simp only [Nat.sub_self, Context.back, hseek, Option.map_some, Option.bind_some]
    exact hsel
  exact final_row_one_of_parse H 33 le_rfl (by decide) P msg T pub _ hfresh hs hp

#print axioms verifier_starts
#print axioms final_row_starts
#print axioms final_row_one
#print axioms final_row_one_of_parse
#print axioms row33_one

end AspisRows40.FinalStarts
end
