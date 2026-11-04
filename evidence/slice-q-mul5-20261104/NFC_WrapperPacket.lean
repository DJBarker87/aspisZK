import NFC_MainPacket
import NFA_FourCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_WrapperPacket
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- SAME source prefix and four actual main packets, in fixed slot order. -/
theorem accepted (q : Slice U8) (g : NEV_DotInputs.Coefficients) (out : Array NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) :
    ∃ window converted fixed a b c d,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        q {«end»:=608#usize}=ok window ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize window=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok fixed ∧
      Nonempty (NFC_MainPacket.Packet fixed g 0#usize a) ∧
      Nonempty (NFC_MainPacket.Packet fixed g 1#usize b) ∧
      Nonempty (NFC_MainPacket.Packet fixed g 2#usize c) ∧
      Nonempty (NFC_MainPacket.Packet fixed g 3#usize d) ∧
      canonE a ∧ canonE b ∧ canonE c ∧ canonE d ∧ out=Array.make 4#usize [a,b,c,d] := by
  obtain ⟨window,converted,fixed,a,b,c,d,select,convert,unwrap,ca,cb,cc,cd,shape⟩:=NFA_FourCuts.actual q g out run
  obtain ⟨pa⟩:=NFC_MainPacket.of_run fixed g 0#usize a ca
  obtain ⟨pb⟩:=NFC_MainPacket.of_run fixed g 1#usize b cb
  obtain ⟨pc⟩:=NFC_MainPacket.of_run fixed g 2#usize c cc
  obtain ⟨pd⟩:=NFC_MainPacket.of_run fixed g 3#usize d cd
  exact ⟨window,converted,fixed,a,b,c,d,select,convert,unwrap,⟨pa⟩,⟨pb⟩,⟨pc⟩,⟨pd⟩,
    (NFC_MainPacket.domains pa).2.2.1,(NFC_MainPacket.domains pb).2.2.1,
    (NFC_MainPacket.domains pc).2.2.1,(NFC_MainPacket.domains pd).2.2.1,shape⟩
#print axioms accepted
end AspisR1.NFC_WrapperPacket
end
