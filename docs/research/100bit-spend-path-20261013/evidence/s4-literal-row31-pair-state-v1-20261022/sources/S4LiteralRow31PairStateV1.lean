import S4LiteralRow31PairsJoinV1

set_option autoImplicit false
noncomputable section

namespace AspisR1.S4LiteralRow31PairStateV1

open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open R0C.V3
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1.QueryFirstRead AspisR1.QuerySampler AspisR1.QueryStateList
open AspisR1.QuerySamplerBridge AspisR1.TranscriptView
open AspisR1.LiteralQuerySampleRunWitness
open AspisR1PublicPreparation.R4Transport2QueryAbsorb
open AspisR1PublicPreparation.R4Transport2OpeningChain
open AspisR1PublicPreparation.R4Transport2QueryPrefix
open AspisR1.R4Transport2ScanComposition
open AspisR1PublicPreparation.TranscriptStep
open AspisR1PublicPreparation.SourceDigestAddresses

theorem row31_success_pair_eq_source_pairs
    {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (hcall : transcript.Transcript.absorb D before 31#u8 payload = ok absorbed)
    (fits : (R4Transport2OpeningChain.framed payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (blocks states : Nat → Bytes32) (hstart : states 0 = absorbed.state)
    (hs : ∀ k < 8,
      D.digest absorbed.hash (readParts (states k) 2#u8) = ok (states (k+1)))
    (hb : ∀ k < 8,
      D.digest absorbed.hash (readParts (states k) 1#u8) = ok (blocks k))
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts))
    (xs : List Nat) (state : State)
    (hout : (AspisV8R19.MemoizedProgramLaw.eval H
      (AspisR1.LiteralByteSampler.samp 31 P
        (.payload (R4Transport2OpeningChain.message payload fits))).toProgram).2 =
      (Value.queries (.ok xs), state)) :
    R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (R4Transport2QueryPrefix.pairs
        (fun k => decodeState (blocks k)) (fun k => decodeState (states k)))
      (decodeState (states 0)) = (.ok xs, state) := by
  let b := R4Transport2OpeningChain.message payload fits
  let H' : Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let qr := R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
    (R4Transport2QueryPrefix.pairs
      (fun k => decodeState (blocks k)) (fun k => decodeState (states k)))
    (decodeState (states 0))
  have hsource := source_query_prefix D before absorbed payload hcall fits P
    (.payload b) rfl hstate blocks states (by simpa [b] using hstart) hs hb H hdigest
  have hmap := congrArg Prod.snd
    (AspisR1.LiteralByteSampler.eval_eq H 31 P (.payload b))
  have hbyteSource :
      (AspisV8R19.MemoizedProgramLaw.eval H
        (AspisR1.LiteralByteSampler.samp 31 P (.payload b)).toProgram).2 =
        UnifiedSampler.liftQuery qr := by
    calc
      _ = (AspisV8R19.OracleProgramOps.mapView Addr.toBytes
        (AspisV8R19.MemoizedProgramLaw.eval H'
          (LiteralTranscript.samp 31 P (.payload b)).toProgram)).2 := hmap
      _ = UnifiedSampler.liftQuery qr := by
        simpa [AspisV8R19.OracleProgramOps.mapView, qr] using hsource
  have he : (Value.queries (.ok xs),state) = UnifiedSampler.liftQuery qr :=
    hout.symm.trans hbyteSource
  have hfirst : (.ok xs : Except Nat (List Nat)) = qr.1 := by
    simpa [UnifiedSampler.liftQuery] using congrArg Prod.fst he
  have hsecond : state = qr.2 := by
    simpa [UnifiedSampler.liftQuery] using congrArg Prod.snd he
  change qr = (.ok xs,state)
  exact (Prod.ext hfirst hsecond).symm

#print axioms row31_success_pair_eq_source_pairs
end AspisR1.S4LiteralRow31PairStateV1
end
