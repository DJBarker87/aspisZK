import NFI_WrapperTrace
import NFF_LoggedDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_WrapperDomains
open Aeneas Aeneas.Std Result NEV_DotCarrier
theorem reached (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (qPlace gPlace : Nat) (out : Array NE 4#usize)
    (canonical : NEV_DotInputs.Canonical g)
    (run : (NFI_WrapperTrace.run oracle tailOracle q g qPlace gPlace).result=ok out) :
    ∃ window converted fixed a b c d,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        q {«end»:=608#usize}=ok window ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize window=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok fixed ∧
      ∃ pa : NFE_NFC_MainPacket.Packet fixed g 0#usize a,
      ∃ pb : NFE_NFC_MainPacket.Packet fixed g 1#usize b,
      ∃ pc : NFE_NFC_MainPacket.Packet fixed g 2#usize c,
      ∃ pd : NFE_NFC_MainPacket.Packet fixed g 3#usize d,
        NFE_WrapperBridge.NativeDomains pa ∧ NFE_WrapperBridge.NativeDomains pb ∧
        NFE_WrapperBridge.NativeDomains pc ∧ NFE_WrapperBridge.NativeDomains pd ∧
        out=Array.make 4#usize [a,b,c,d] := by
  exact NFF_LoggedDomains.four oracle law tailOracle tailLaw q g out canonical
    ((NFI_WrapperTrace.erased oracle tailOracle q g qPlace gPlace).symm.trans run)
#print axioms reached
end AspisR1.NFI_WrapperDomains
end
