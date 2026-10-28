import NCL_DriverCuts
import DrvC_FirstPure
import Tx1Q_Initial
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_InitialDomain
open Aeneas Aeneas.Std Result DrvC_Installation
attribute [local irreducible] currentInstalled

/-- Discharge constructor domains from the actual installed constructor cut.
No independent64-element/canonical initial vector is supplied by the caller. -/
theorem source {F C : Type} (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (cut : NCL_DriverCuts.Cuts (currentInstalled c) (currentDigest c) semantic pub proof () saved) :
    c.reserved=true ∧
    (Tx1Q_Carriers.accumulator cut.initial).weights.val=List.replicate 64 Port2_Initial.zeroK ∧
    (Tx1Q_Carriers.accumulator cut.initial).rhs=Port2_Initial.zeroE ∧
    (Tx1Q_Carriers.accumulator cut.initial).power=Port2_Initial.oneK ∧
    (Tx1Q_Carriers.accumulator cut.initial).next=0#usize := by
  have call := cut.initial_call
  change Tx1Q_PrefixInstall.initial c.reserved .S2=ok (.Ok cut.initial) at call
  exact Tx1Q_Initial.raw c.reserved (Tx1Q_Carriers.accumulator cut.initial)
    (Tx1Q_PrefixInstall.initial_success c.reserved cut.initial call)
#print axioms source
end AspisR1.NCL_InitialDomain
end
