import NFM_Cuts
import NFI_SingleDomains
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFM_Single
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
abbrev Cut (input : Input) := Sum NFM_Cuts.Cut (NFI_TailTrace.Cut input)

def main (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    M (Cut input) NFI_OuterCut.Returned :=
  let observed := NFM_Cuts.sequence oracle input [0,1,2,3,4,5,6]
    (Array.repeat 8#usize 0#u64)
  ⟨NFI_OuterTrace.pack input observed.result,observed.cuts.map Sum.inl⟩

theorem main_same (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    (main oracle input).result=(NFI_SingleTrace.main oracle input).result := by
  rw [NFI_SingleTrace.main_erased]
  exact congrArg (NFI_OuterTrace.pack input)
    (NFM_Cuts.main oracle input (Array.repeat 8#usize 0#u64))

def tail (oracle : NFF_ProductCall.Oracle) (input : Input) : M (Cut input) NEV_DotCarrier.NE :=
  let observed := NFI_TailTrace.run oracle input
  ⟨observed.result,observed.cuts.map Sum.inr⟩

def run (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (input : Input) : M (Cut input) NEV_DotCarrier.NE := do
  let out ← main oracle input
  let head ← lift (NFE_NFA_SuffixFactor.scalarFinish out.limbs)
  let t ← tail tailOracle input
  lift (FIo_Native.aspis_core.field.wide_exact.WideExact.add head t)

theorem same (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (input : Input) :
    (run oracle tailOracle input).result=(NFI_SingleTrace.run oracle tailOracle input).result := by
  simp only [run,NFI_SingleTrace.run,erase_bind,erase_lift,main_same,tail,NFI_SingleTrace.tail]

theorem emitted (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (input : Input) (canonical : NEV_DotInputs.Canonical input.g) :
    (run oracle tailOracle input).result=FIp_NativeDots.fast_dots.four_dots_one
      input.q input.g input.slot := by
  rw [same,NFI_SingleTrace.emitted oracle law tailOracle tailLaw input canonical]

theorem domains (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (input : Input) (out : NEV_DotCarrier.NE)
    (canonical : NEV_DotInputs.Canonical input.g)
    (success : (run oracle tailOracle input).result=ok out) :
    ∃ p : NFE_NFC_MainPacket.Packet input.q input.g input.slot out,
      NFE_WrapperBridge.NativeDomains p := by
  exact NFI_SingleDomains.reached oracle law tailOracle tailLaw input out canonical
    ((same oracle tailOracle input).symm.trans success)

#print axioms main_same
#print axioms same
#print axioms emitted
#print axioms domains
end AspisR1.NFM_Single
end
