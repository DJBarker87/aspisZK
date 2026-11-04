import NFI_SingleTrace
import NFF_FullWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_WrapperTrace
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
abbrev Cut := (input : Input) × NFI_SingleTrace.Cut input

def child (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (input : Input) : M Cut NEV_DotCarrier.NE :=
  let observed := NFI_SingleTrace.run oracle tailOracle input
  ⟨observed.result,observed.cuts.map fun event => ⟨input,event⟩⟩

def run (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (qPlace gPlace : Nat) :
    M Cut (Array NEV_DotCarrier.NE 4#usize) := do
  let window ← lift (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    q {«end»:=608#usize})
  let converted ← lift (core.array.TryFromSharedArraySlice.try_from 608#usize window)
  let fixed ← lift (core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted)
  let a ← child oracle tailOracle ⟨fixed,g,0#usize,qPlace,gPlace⟩
  let b ← child oracle tailOracle ⟨fixed,g,1#usize,qPlace,gPlace⟩
  let c ← child oracle tailOracle ⟨fixed,g,2#usize,qPlace,gPlace⟩
  let d ← child oracle tailOracle ⟨fixed,g,3#usize,qPlace,gPlace⟩
  pure (Array.make 4#usize [a,b,c,d])

theorem erased (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (qPlace gPlace : Nat) :
    (run oracle tailOracle q g qPlace gPlace).result=NFF_FullWrapper.run oracle tailOracle q g := by
  simp only [run,NFF_FullWrapper.run,erase_bind,erase_lift,erase_pure,child,NFI_SingleTrace.erased]
  try rfl

theorem headline (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Slice U8) (g : NEV_DotInputs.Coefficients) (qPlace gPlace : Nat)
    (domain : NEV_DotInputs.Canonical g) :
    (run oracle tailOracle q g qPlace gPlace).result=NEI_FourWrapper.fast_dots.four_dots q g := by
  rw [erased,NFF_FullWrapper.headline oracle law tailOracle tailLaw q g domain]

#print axioms erased
#print axioms headline
end AspisR1.NFI_WrapperTrace
end
