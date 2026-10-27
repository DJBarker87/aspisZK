import RPu_FJo_FixedAssemble
import RPu_FJl_SlotReads
import RPu_FJl_TailWindow1
import RPu_FJl_TailWindow2
import RPu_FJl_WindowArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_C2SlotDecode
open Aeneas Aeneas.Std Result MultiproofConeCanonical
/-- Both C2 coordinates are read by the SAME successful source slot. -/
theorem value (q : Array U8 608#usize) (g : Array FIo_FieldBridge.NE 29#usize)
    (s : Fin 4) (slot : Usize) (hs : slot.val=s.val) (out : FIo_FieldBridge.NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) :
    ∃ c, MixedLeafDecoder.decodeC2Slot
      (((((bytesOf q.val).drop 480).take 128).drop (32*s.val)).take 32)=some c := by
  obtain ⟨reads,v0,v1,v2,h0,h1,h2⟩ := FJl_SlotReads.reached q g slot out run
  let bytes := ((((bytesOf q.val).drop 480).take 128).drop (32*s.val)).take 32
  have qlen : q.val.length=608 := q.property
  apply FJo_FixedAssemble.value ExactLeafFieldCodec.decodeQM31 16 2 bytes
  · simp only [bytes,bytesOf,List.length_take,List.length_drop,List.length_map,qlen]
    have := s.isLt
    omega
  · intro l
    have window := FJl_WindowArithmetic.c2 (bytesOf q.val) s.val l.val s.isLt l.isLt
    change (((((bytesOf q.val).drop 480).take 128).drop (32*s.val)).take 32 |>.drop (16*l.val) |>.take 16)=_ at window
    rw [window]
    have t1 := FJl_TailWindow1.value q slot (by rw [hs];exact s.isLt) v1 h1
    have t2 := FJl_TailWindow2.value q slot (by rw [hs];exact s.isLt) v2 h2
    rw [hs] at t1 t2
    fin_cases l
    · exact ⟨_,t1⟩
    · exact ⟨_,t2⟩
#print axioms value
end AspisR1.FJo_C2SlotDecode
end
