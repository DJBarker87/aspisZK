import S9ConcreteArithmeticAcceptedRootV1
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9ConcreteQMMulAcceptedRootV1
open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1
open AspisR1.S9ConcreteArithmeticAcceptedRootV1

theorem qmMul_success (x y z : Q) (hx : CanonicalQ x) (hy : CanonicalQ y)
    (h : @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x y = .ok z) :
    CanonicalQ z ∧ decodeQ z = decodeQ x * decodeQ y := by
  have hcurrent : @FieldOps.qmMul currentFieldOps x y = .ok z :=
    (AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current x y).symm.trans h
  exact @QMSemantics.mul_success ExactQM inferInstance currentFieldOps
    currentQMSemantics x y z hx hy hcurrent

#print axioms qmMul_success
end AspisR1.S9ConcreteQMMulAcceptedRootV1
