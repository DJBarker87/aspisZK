import RPz7_RawSourceLiteralSamplerStep
import RPz7_ExtractedSourceFull25Frames
import R1LiteralTranscript
import R1SelectedTranscriptParams

set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.SourceLiteralTraceLift

open Aeneas Aeneas.Std Result
open AspisR1
open AspisR1.TranscriptView
open AspisR1.LiteralTranscript
open AspisR1.SelectedTranscriptParams
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex
open AspisV8R15.ExactTowerBase
open AspisR1.UnifiedPayloadValue

def sourceChallenge {H : Type} {D : aspis_core.Digest32 H}
    {pre : r1_wire.Prefix} (c : SourceFull25.Call D pre) : AspisWideTower.WideExact :=
  algebraMap QM31Exact AspisWideTower.WideExact
    (ExtractedCurrentQM31Exact.decode
      (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld c.q)))

def sourcePrefix {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pre : r1_wire.Prefix} : (i : Nat) → (P : LiteralTranscript.Prefix) →
    (cs : List (SourceFull25.Call D pre)) →
    (bound : ∀ c ∈ cs, (SourceDigestAddresses.rawBytes c.record.framed).length ≤
      SelectedTranscriptParams.params.D) → LiteralTranscript.Prefix
  | _, P, [], _ => P
  | i, P, c :: cs, bound =>
      sourcePrefix (i + 1) (P.ext
        (.payload ⟨SourceDigestAddresses.rawBytes c.record.framed, bound c (by simp)⟩)
        (.ordinary (sourceChallenge c), decodeState c.after.state)) cs
        (fun d hd => bound d (List.mem_cons_of_mem _ hd))
def literalPrefix {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pre : r1_wire.Prefix} (Hbytes : AspisV8R19.DuplexFrames.Bytes → State) :
    (i : Nat) → (P : LiteralTranscript.Prefix) →
    (cs : List (SourceFull25.Call D pre)) →
    (bound : ∀ c ∈ cs, (SourceDigestAddresses.rawBytes c.record.framed).length ≤
      SelectedTranscriptParams.params.D) → LiteralTranscript.Prefix
  | _, P, [], _ => P
  | i, P, c :: cs, bound =>
      let mm : SelectedTranscriptParams.Message :=
        ⟨SourceDigestAddresses.rawBytes c.record.framed, bound c (by simp)⟩
      literalPrefix Hbytes (i + 1) (P.ext (.payload mm)
        (AspisV8R19.MemoizedProgramLaw.eval
          (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
          (LiteralTranscript.samp i P (.payload mm)).toProgram).2) cs
        (fun d hd => bound d (List.mem_cons_of_mem _ hd))

/-- The positive-row source trace and literal sampler build the same extended
prefix. The first row is deliberately excluded: it uses the dedicated public
initializer and is handled by a separate row-zero bridge. -/
theorem positive_trace_simulation
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (hash : Hash) (hbeforeHash : before.hash = hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (Hbytes : AspisV8R19.DuplexFrames.Bytes → State)
    (horacle : ∀ a : Addr SelectedTranscriptParams.L,
      SourceDigestOracle.oracle D before.hash pubInput root length a = Hbytes a.toBytes)
    (bound : ∀ c ∈ cs,
      (SourceDigestAddresses.rawBytes c.record.framed).length ≤
        SelectedTranscriptParams.params.D)
    (i : Nat) (P : LiteralTranscript.Prefix)
    (hi0 : i ≠ 0) (hcount : i + cs.length ≤ 25)
    (hrow : before.next_row.val = i)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state) :
    literalPrefix Hbytes i P cs bound = sourcePrefix i P cs bound ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (sourcePrefix i P cs bound)) =
          decodeState after.state := by
  revert bound i P hi0 hcount hrow hstate hbeforeHash
  induction run with
  | nil self =>
      intro hbeforeHash bound i P hi0 hcount hrow hstate
      exact ⟨rfl, by simpa only [sourcePrefix] using hstate⟩
  | @cons tailAfter tailCalls c tail ih =>
      intro hbeforeHash bound i P hi0 hcount hrow hstate
      have hlenPos : 0 < (c :: tailCalls).length := by simp
      have hlt : i < 25 := by
        have hh : i + (c :: tailCalls).length ≤ 25 := hcount
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlenPos) hh
      have hrowc : c.row.val = i := by
        calc
          c.row.val = c.record.row.val := congrArg (fun x => x.val) c.record_row.symm
          _ = c.before.next_row.val := congrArg (fun x => x.val) c.before_row
          _ = i := hrow
      have hnext : c.after.next_row.val = i + 1 := by
        have hn : c.after.next_row = c.next := by rw [c.carried]
        calc
          c.after.next_row.val = c.next.val := congrArg (fun x => x.val) hn
          _ = c.record.row.val + 1 := c.next_row
          _ = c.row.val + 1 := congrArg (fun x => x.val + 1) c.record_row
          _ = i + 1 := by rw [hrowc]
      have hbound :
          (SourceDigestAddresses.rawBytes c.record.framed).length ≤
            SelectedTranscriptParams.params.D := bound c (by simp)
      let mm : SelectedTranscriptParams.Message :=
        ⟨SourceDigestAddresses.rawBytes c.record.framed, hbound⟩
      have hstep := SourceLiteralSamplerStep.call_simulates_literal_payload
        (SourceFull25.Trace.cons c tail) c (by simp) pubInput root length Hbytes
        (by simpa only [hbeforeHash] using horacle)
        bound i hlt hi0 hrowc P (.payload mm) mm rfl hstate rfl
      change Value.ordinary (sourceChallenge c) =
          (AspisV8R19.MemoizedProgramLaw.eval
            (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
            (LiteralTranscript.samp i P (.payload mm)).toProgram).2.1 ∧
        decodeState c.after.state =
          (AspisV8R19.MemoizedProgramLaw.eval
            (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
            (LiteralTranscript.samp i P (.payload mm)).toProgram).2.2 at hstep
      have hpair :
          (AspisV8R19.MemoizedProgramLaw.eval
            (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
            (LiteralTranscript.samp i P (.payload mm)).toProgram).2 =
            (Value.ordinary (sourceChallenge c), decodeState c.after.state) :=
        Prod.ext hstep.1.symm hstep.2.symm
      let Pnext := P.ext (.payload mm)
        ((AspisV8R19.MemoizedProgramLaw.eval
          (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
          (LiteralTranscript.samp i P (.payload mm)).toProgram).2)
      have hstateNext : UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix Pnext) = decodeState c.after.state := by
        dsimp [Pnext]
        rw [LiteralTranscript.erasePrefix_ext, UnifiedSampler.stateOf_ext]
        exact hstep.2.symm
      have hcountTail : (i + 1) + tailCalls.length ≤ 25 := by
        simp only [List.length_cons] at hcount
        omega
      have hboundTail : ∀ d ∈ tailCalls,
          (SourceDigestAddresses.rawBytes d.record.framed).length ≤
            SelectedTranscriptParams.params.D := by
        intro d hd
        exact bound d (List.mem_cons_of_mem _ hd)
      have hhashNext : c.after.hash = c.before.hash := by
        rw [c.carried]
      have horacleNext : ∀ a : Addr SelectedTranscriptParams.L,
          SourceDigestOracle.oracle D c.after.hash pubInput root length a = Hbytes a.toBytes := by
        intro a
        rw [hhashNext]
        exact horacle a
      have hafterHash : c.after.hash = hash := hhashNext.trans hbeforeHash
      have htail := ih horacleNext hafterHash hboundTail (i + 1) Pnext (by omega)
        hcountTail hnext hstateNext
      have hprefixNext : Pnext = P.ext (.payload mm)
          (Value.ordinary (sourceChallenge c), decodeState c.after.state) := by
        dsimp [Pnext]
        rw [hpair]
      constructor
      · change literalPrefix Hbytes (i + 1) Pnext tailCalls hboundTail =
          sourcePrefix (i + 1)
            (P.ext (.payload mm)
              (Value.ordinary (sourceChallenge c), decodeState c.after.state))
            tailCalls hboundTail
        rw [← hprefixNext]
        exact htail.1
      · simp only [sourcePrefix]
        rw [← hprefixNext]
        exact htail.2

end AspisR1PublicPreparation.SourceLiteralTraceLift
end
