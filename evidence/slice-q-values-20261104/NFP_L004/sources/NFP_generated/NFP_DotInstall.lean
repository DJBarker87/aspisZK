import NFP_QueryCuts
import NFM_ProductInstance
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_DotInstall
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody NFP_QueryCuts

def oracle (ops : Ops) (qPlace gPlace : Nat) : Ops :=
 {ops with op20 := fun q g =>
  (NFI_WrapperTrace.run NFM_ProductInstance.mainProduct NFM_ProductInstance.tailProduct q g qPlace gPlace).result}
def cohort (ops : Ops) : Ops := {ops with op20 := NEI_FourWrapper.fast_dots.four_dots}

/-- Substitution uses the existing CLOSED NFM wrapper on the SAME q and g;
canonicality is an input predicate, not a separately chosen successful packet. -/
theorem head (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : NEV_DotInputs.Coefficients)
 (qPlace gPlace : Nat) (canonical : NEV_DotInputs.Canonical g) :
 NFP_QueryCuts.head (oracle ops qPlace gPlace) proof p a g =
 NFP_QueryCuts.head (cohort ops) proof p a g := by
 simp only [NFP_QueryCuts.head,oracle,cohort,
  NFM_ProductInstance.wrapper _ g qPlace gPlace canonical]
 rfl
#print axioms head
end AspisR1.NFP_DotInstall
end
