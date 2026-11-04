import NFF_FullWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_LoggedDomains
open Aeneas Aeneas.Std Result NEV_DotCarrier

/-- Every callee domain follows from the same logged computation's accepted
Result and the one root g predicate. No inner successful reply is supplied. -/
theorem one (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (out : NE) (canonical : NEV_DotInputs.Canonical g)
    (run : NFF_FullOne.run oracle tailOracle q g slot=ok out) :
    ∃ p : NFE_NFC_MainPacket.Packet q g slot out, NFE_WrapperBridge.NativeDomains p := by
  have actual := (NFF_FullOne.replay oracle law tailOracle tailLaw q g canonical slot).symm.trans run
  obtain ⟨p⟩:=NFE_NFC_MainPacket.of_run q g slot out actual
  exact ⟨p,NFE_WrapperBridge.domains p canonical⟩

/-- Original prefix/conversion, all four packets and all their native input
restrictions are derived together; these are emitted-model domains, not a
native physical correspondence assumption or conclusion. -/
theorem four (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (out : Array NE 4#usize)
    (canonical : NEV_DotInputs.Canonical g)
    (run : NFF_FullWrapper.run oracle tailOracle q g=ok out) :
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
  have actual := (NFF_FullWrapper.headline oracle law tailOracle tailLaw q g canonical).symm.trans run
  exact NFE_WrapperBridge.four q g out canonical actual

#print axioms one
#print axioms four
end AspisR1.NFF_LoggedDomains
end
