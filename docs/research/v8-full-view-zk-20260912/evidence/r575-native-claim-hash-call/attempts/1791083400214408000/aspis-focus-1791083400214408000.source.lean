import AspisV8R19.R573ClaimPrefixExecution
import AspisV8R19.R206CurrentAbsorbHashCall
import AspisV8R19.R152WrappingBounds

set_option autoImplicit false
namespace AspisV8R19.R575NativeClaimHashCall
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open R573ClaimPrefixExecution

def toCurrentTranscript (t : NTranscript) :
    AspisR156FullFreeze.aspis_core.transcript.Transcript := ⟨t.state, t.hash⟩

def fromCurrentTranscript (t : AspisR156FullFreeze.aspis_core.transcript.Transcript) :
    NTranscript := ⟨t.state, t.hash⟩

theorem checked_limit : (192#usize - 34#usize : Result Usize) = .ok 158#usize := by
  have h := UScalar.sub_spec (x := (192#usize : Usize)) (y := 34#usize) (by scalar_tac)
  obtain ⟨x, hx, hval⟩ := spec_imp_exists h
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  simpa using hval.1

theorem absorb_map_short (t : NTranscript) (label : U8) (data : Slice U8)
    (hd : data.val.length ≤ 158) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.absorb t label data =
      (do
        let next ← AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb
          (toCurrentTranscript t) label data
        ok (fromCurrentTranscript next)) := by
  have hadd : (34#usize + data.len : Result Usize) =
      .ok (Std.Usize.wrapping_add 34#usize data.len) := by
    apply R152WrappingBounds.checked_add_eq_wrapping
    have hmax : 192 ≤ Usize.max := by scalar_tac
    simp only [Slice.len_val, Slice.length, show (34#usize : Usize).val = 34 from rfl]
    omega
  have hwrap : Std.Usize.wrapping_sub 192#usize 34#usize = 158#usize := by
    apply UScalar.eq_of_val_eq
    simpa only [AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES]
      using R137TranscriptPrimitiveBridge.packed_payload_limit
  have hshort : data.len ≤ (158#usize : Usize) := hd
  cases t
  simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.absorb,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb,
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.DOM_ABSORB,
    AspisR156FullFreeze.aspis_core.transcript.DOM_ABSORB,
    checked_limit, hadd, hwrap, hshort, if_true, toCurrentTranscript,
    fromCurrentTranscript, lift, bind_assoc_eq, bind_tc_ok]

theorem claim_length (q : NQM31) : (claimBytes q).length = 18 := by
  simp only [claimBytes, List.length_cons, R144BeforeOodBytesBridge.qm31Bytes_length]

theorem claim_absorb_execution (t : NTranscript) (q : NQM31) (data : Slice U8)
    (hdata : data.val = claimBytes q) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.absorb t 31#u8 data =
      (do
        let next ← t.hash (R205AbsorbHashCall.packedMessage t.state 31#u8 data (by
          rw [hdata, claim_length]; omega))
        ok {t with state := next}) := by
  have hd : data.val.length ≤ 158 := by rw [hdata, claim_length]; omega
  have hshort : data.len ≤
      AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize := by
    change data.val.length ≤ _
    have hlim : (AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize).val = 158 := by
      simpa only [AspisR156FullFreeze.aspis_core.transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
        AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES]
        using R137TranscriptPrimitiveBridge.packed_payload_limit
    rw [hlim]
    exact hd
  rw [absorb_map_short _ _ _ hd, R206CurrentAbsorbHashCall.short_execution _ _ _ hshort]
  cases t
  simp only [toCurrentTranscript, fromCurrentTranscript, bind_assoc_eq, bind_tc_ok]

#print axioms checked_limit
#print axioms absorb_map_short
#print axioms claim_length
#print axioms claim_absorb_execution
end AspisV8R19.R575NativeClaimHashCall
