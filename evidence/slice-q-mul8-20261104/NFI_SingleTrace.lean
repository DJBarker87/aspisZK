import NFI_InnerActual
import NFI_OuterActual
import NFI_TailTrace
import NFI_PrivateCuts
import NFF_FullOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_SingleTrace
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
abbrev Cut (input : Input) := Sum NFI_OuterCut.Cut (NFI_TailTrace.Cut input)

def main (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    M (Cut input) NFI_OuterCut.Returned :=
  let observed := NFI_OuterTrace.run oracle 7
    ⟨input,NFA_Iterator.value 0,Array.repeat 8#usize 0#u64⟩
  ⟨observed.1,observed.2.map Sum.inl⟩

def tail (oracle : NFF_ProductCall.Oracle) (input : Input) : M (Cut input) NEV_DotCarrier.NE :=
  let observed := NFI_TailTrace.run oracle input
  ⟨observed.result,observed.cuts.map Sum.inr⟩

def run (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (input : Input) : M (Cut input) NEV_DotCarrier.NE := do
  let out ← main oracle input
  let head ← lift (NFE_NFA_SuffixFactor.scalarFinish out.limbs)
  let t ← tail tailOracle input
  lift (FIo_Native.aspis_core.field.wide_exact.WideExact.add head t)

theorem main_erased (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    (main oracle input).result=NFI_OuterTrace.pack input
      (NFF_LoggedOuterLoop.run oracle input.q input.g input.slot 7
        (NFA_Iterator.value 0) (Array.repeat 8#usize 0#u64)) := by
  exact NFI_OuterTrace.replay oracle 7 _

theorem erased (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (input : Input) :
    (run oracle tailOracle input).result=NFF_FullOne.run oracle tailOracle
      input.q input.g input.slot := by
  have right {T : Type} (r : Result T) : (do let x ← r; ok x)=r := by cases r <;> rfl
  have pack_bind {T : Type} (r : Result (Array U64 8#usize))
      (f : NFI_OuterCut.Returned → Result T) :
      (do let a ← NFI_OuterTrace.pack input r; f a)=
        (do let a ← r; f ⟨input,a⟩) := by cases r <;> rfl
  simp only [run,erase_bind,erase_lift,main_erased,tail,NFI_TailTrace.erased,
    pack_bind,NFF_FullOne.run,right]
  try rfl

theorem emitted (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (input : Input) (canonical : NEV_DotInputs.Canonical input.g) :
    (run oracle tailOracle input).result=FIp_NativeDots.fast_dots.four_dots_one
      input.q input.g input.slot := by
  rw [erased,NFF_FullOne.replay oracle law tailOracle tailLaw _ _ canonical]

#print axioms main_erased
#print axioms erased
#print axioms emitted
end AspisR1.NFI_SingleTrace
end
