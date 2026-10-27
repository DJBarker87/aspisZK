import RPu_FJo_FixedAssemble
import RPu_FJo_ScalarDecode
import RPu_FJl_SlotReads
import RPu_FJl_TailWindow0
import RPu_FJl_WindowArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_C1SlotDecode
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- The complete C1 slot decoder succeeds from the SAME native reads. -/
theorem value (q : Array U8 608#usize) (g : Array FIo_FieldBridge.NE 29#usize)
    (s : Fin 4) (slot : Usize) (hs : slot.val=s.val) (out : FIo_FieldBridge.NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    ∃ c, MixedLeafDecoder.decodeC1Slot
      ((((bytesOf q.val).take 480).drop (120*s.val)).take 120)=some c := by
  obtain ⟨reads,v0,v1,v2,h0,h1,h2⟩ := FJl_SlotReads.reached q g slot out run
  let bytes := (((bytesOf q.val).take 480).drop (120*s.val)).take 120
  have qlen : q.val.length=608 := q.property
  have size : (bytes.take 104).length=4*26 := by
    simp only [bytes,bytesOf,List.length_take,List.length_drop,List.length_map,qlen]
    have := s.isLt
    omega
  obtain ⟨words,hw⟩ := FJo_FixedAssemble.value ExactLeafFieldCodec.decodeM31 4 26 (bytes.take 104) size (by
    intro l
    have h := FJo_ScalarDecode.value q slot reads l
    rw [hs] at h
    simpa only [bytes,FJl_WindowArithmetic.scalar _ _ _ s.isLt l.isLt,OraclePortCompactDraft.slice] using h)
  have ht := FJl_TailWindow0.value q slot (by rw [hs];exact s.isLt) v0 h0
  rw [hs] at ht
  refine ⟨(words,AspisR1CurrentWide.Proof.decodeQM (FIo_FieldBridge.qm v0)),?_⟩
  unfold MixedLeafDecoder.decodeC1Slot
  rw [hw]
  have tail : bytes.drop 104=OraclePortCompactDraft.slice (bytesOf q.val) (120*s.val+104) 16 :=
    FJl_WindowArithmetic.c1tail _ _ s.isLt
  change (ExactLeafFieldCodec.decodeQM31 (bytes.drop 104)).bind (fun t=>some (words,t))=_
  rw [tail,ht]
  rfl
#print axioms value
end AspisR1.FJo_C1SlotDecode
end
