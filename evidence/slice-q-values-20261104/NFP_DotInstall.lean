import NFP_QueryCuts
import NFM_ProductInstance
import RPz7_FIp_DotsAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_DotInstall
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody NFP_QueryCuts

def dot (q : Slice U8) (g : Array E 29#usize) (qPlace gPlace : Nat) : Result Dots := do
 let out ← (NFI_WrapperTrace.run NFM_ProductInstance.mainProduct NFM_ProductInstance.tailProduct
  q (FIp_DotsAdapter.toArray g) qPlace gPlace).result
 ok (FIp_DotsAdapter.fromArray out)
def oracle (ops : Ops) (qPlace gPlace : Nat) : Ops :=
 {ops with op20 := fun q g => dot q g qPlace gPlace}
def cohort (ops : Ops) : Ops := {ops with op20 := FIp_DotsAdapter.dots}

theorem dot_result (q : Slice U8) (g : Array E 29#usize)
 (qPlace gPlace : Nat) (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) :
 dot q g qPlace gPlace = FIp_DotsAdapter.dots q g := by
 unfold dot FIp_DotsAdapter.dots
 rw [NFM_ProductInstance.wrapper _ _ _ _ canonical]
 rfl

/-- Substitution uses the existing CLOSED NFM wrapper on the SAME q and g;
canonicality is an input predicate, not a separately chosen successful packet. -/
theorem head (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (qPlace gPlace : Nat) (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) :
 NFP_QueryCuts.head (oracle ops qPlace gPlace) proof p a g =
 NFP_QueryCuts.head (cohort ops) proof p a g := by
 simp only [NFP_QueryCuts.head,oracle,cohort,
  dot_result _ g qPlace gPlace canonical]
#print axioms dot_result
#print axioms head
end AspisR1.NFP_DotInstall
end
