import NFF_LoggedOuterLoop
import NFF_LoggedTail
import NFE_NFA_SuffixFactor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_FullOne
open Aeneas Aeneas.Std Result

def run (oracle : NFF_LoggedEight.Oracle) (tailOracle : NFF_ProductCall.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize) : Result NEV_DotCarrier.NE := do
  let limbs ← NFF_LoggedOuterLoop.run oracle q g slot 7 (NFA_Iterator.value 0)
    (Array.repeat 8#usize 0#u64)
  let head ← NFE_NFA_SuffixFactor.scalarFinish limbs
  let tail ← NFF_LoggedTail.run tailOracle q g slot
  FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail

/-- Both main and tail arithmetic are primitive logged products. Every
continuation is the emitted one, including every error and final return. -/
theorem replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize) :
    run oracle tailOracle q g slot=FIp_NativeDots.fast_dots.four_dots_one q g slot := by
  have zero : NFE_NFA_FoldEight.Bound (Array.repeat 8#usize 0#u64) 0 := by
    intro x hx
    change x∈List.replicate 8 (0#u64) at hx
    have same : x=0#u64 := (List.mem_replicate.mp hx).2
    subst x
    simp
  have loopEq := NFF_LoggedOuterLoop.replay oracle law q g domain slot 7
    (NFA_Iterator.value 0) (Array.repeat 8#usize 0#u64) 0 rfl rfl rfl rfl zero
  rw [NFE_NFA_SuffixFactor.body]
  simp only [run,NFA_Iterator.initial,bind_tc_ok,loopEq,NFF_LoggedTail.replay tailOracle tailLaw]

#print axioms replay
end AspisR1.NFF_FullOne
end
