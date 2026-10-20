import RawSourceGlobalOracleCoupling

/-! Positive source traces under the same consistent global byte-oracle log.
Unlike the older constructed-source-oracle bridge, no unqueried-address
agreement premise or fixed digest dictionary hash is needed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceGlobalOracleTrace
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.TranscriptView
open AspisR1.LiteralTranscript AspisR1.SelectedTranscriptParams
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex
open AspisV8R15.ExactTowerBase
open AspisR1.UnifiedPayloadValue
open SourceLiteralTraceLift RawSourceC2CutBinding

theorem positive_trace_simulation
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (Hbytes : AspisV8R19.DuplexFrames.Bytes → State)
    (tr : List (AspisV8R19.DuplexFrames.Bytes × State))
    (hsource : sourceLog cs ⊆ tr) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
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
  revert hsource bound i P hi0 hcount hrow hstate
  induction run with
  | nil self =>
      intro hsource bound i P hi0 hcount hrow hstate
      exact ⟨rfl, by simpa only [sourcePrefix] using hstate⟩
  | @cons tailAfter tailCalls c tail ih =>
      intro hsource bound i P hi0 hcount hrow hstate
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
      have hstep := SourceGlobalOracleCoupling.call_simulates_literal_payload
        (c :: tailCalls) c (by simp) Hbytes tr hsource hcons
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
      have hsourceTail : sourceLog tailCalls ⊆ tr := by
        intro q hq
        apply hsource
        rcases List.mem_flatMap.mp hq with ⟨d,hd,hqd⟩
        exact List.mem_flatMap.mpr ⟨d,List.mem_cons_of_mem c hd,hqd⟩
      have htail := ih hsourceTail hboundTail (i + 1) Pnext (by omega)
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

#print axioms positive_trace_simulation
end AspisR1PublicPreparation.SourceGlobalOracleTrace
end
