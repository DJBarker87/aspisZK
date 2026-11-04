import NFE_DotBridge
import NEI_FourWrapperLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_WrapperBridge
open Aeneas Aeneas.Std Result NEV_DotCarrier

def NativeDomains {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients}
    {slot : Usize} {out : NE} (p : NFE_NFC_MainPacket.Packet q g slot out) : Prop :=
  (canonE p.tailPacket.args0.1 ∧ canonQ p.tailPacket.args0.2 ∧
    canonE p.tailPacket.args1.1 ∧ canonQ p.tailPacket.args1.2 ∧
    canonE p.tailPacket.args2.1 ∧ canonQ p.tailPacket.args2.2) ∧
  (p.tailPacket.state0.count.val<3 ∧ p.tailPacket.state1.count.val<3 ∧
    p.tailPacket.state2.count.val<3) ∧
  (canonE p.head ∧ canonE p.tail ∧ canonE out)

theorem domains {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients}
    {slot : Usize} {out : NE} (p : NFE_NFC_MainPacket.Packet q g slot out)
    (canonical : NEV_DotInputs.Canonical g) : NativeDomains p := by
  obtain ⟨a,b,c,_⟩ := NFE_NFC_MainPacket.domains p
  exact ⟨NFE_NFC_PacketDomains.inputs p.tailPacket canonical,
    NFE_NFC_PacketDomains.native_counts p.tailPacket,a,b,c⟩

/-- Four exact ordered child calls of the SAME extracted wrapper. Every native
callee domain follows from one root coefficient predicate and that call's
packet, rather than being supplied as four independent successful witnesses. -/
theorem four (q : Slice U8) (g : NEV_DotInputs.Coefficients) (out : Array NE 4#usize)
    (canonical : NEV_DotInputs.Canonical g)
    (run : NEI_FourWrapper.fast_dots.four_dots q g=ok out) :
    ∃ window converted fixed a b c d,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        q {«end»:=608#usize}=ok window ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize window=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok fixed ∧
      ∃ pa : NFE_NFC_MainPacket.Packet fixed g 0#usize a,
      ∃ pb : NFE_NFC_MainPacket.Packet fixed g 1#usize b,
      ∃ pc : NFE_NFC_MainPacket.Packet fixed g 2#usize c,
      ∃ pd : NFE_NFC_MainPacket.Packet fixed g 3#usize d,
        NativeDomains pa ∧ NativeDomains pb ∧ NativeDomains pc ∧ NativeDomains pd ∧
        out=Array.make 4#usize [a,b,c,d] := by
  rw [NEI_FourWrapperLaw.emitted_to_cohort] at run
  obtain ⟨window,converted,fixed,a,b,c,d,select,convert,unwrap,
    ⟨pa⟩,⟨pb⟩,⟨pc⟩,⟨pd⟩,_,_,_,_,shape⟩ := NFE_NFC_WrapperPacket.accepted q g out run
  exact ⟨window,converted,fixed,a,b,c,d,select,convert,unwrap,
    pa,pb,pc,pd,domains pa canonical,domains pb canonical,
    domains pc canonical,domains pd canonical,shape⟩

#print axioms domains
#print axioms four
end AspisR1.NFE_WrapperBridge
end
