import FIp_Install
import FIp_DotsOutputCanonical
import FIp_EqualityValue
import FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_InstalledLaws
open Aeneas Aeneas.Std Result DrvC_Installation
abbrev E := AspisR1Stage2.Stage2Finish.E

theorem first_fold {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (alpha out : E) (v : Array E 4#usize) (inverse : Array U32 5#usize)
    (run : (FIp_Install.configuration err c r).query.op17 alpha v inverse=ok out) :
    Port4C_QueryArithmetic.CanonE out :=
  (FIp_CircleQuery.exact_circle alpha v inverse out run).2

theorem dots {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (q : Slice U8) (g : Array E 29#usize) (out : Array E 4#usize)
    (run : (FIp_Install.configuration err c r).query.op20 q g=ok out) :
    ∀ x∈out.val,Port4C_QueryArithmetic.CanonE x := FIp_DotsOutputCanonical.all q g out run

theorem compared {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (x y : E)
    (run : core.cmp.PartialEq.ne.trait_default (FIp_Install.configuration err c r).query.widePartialEq x y=ok false) :
    x=y := FIp_EqualityValue.ne_false x y run

theorem semantic_add {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (x y z : FIp_SemanticArithmetic.MQ) (hx : FIp_SemanticValues.Canon x) (hy : FIp_SemanticValues.Canon y)
    (run : (FIp_Install.configuration err c r).boundaries.add x y=ok z) :
    FIp_SemanticValues.Canon z ∧ FIp_SemanticValues.decode z=FIp_SemanticValues.decode x+FIp_SemanticValues.decode y :=
  FIp_SemanticValues.add x y z hx hy run

theorem semantic_mul {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (x y z : FIp_SemanticArithmetic.MQ) (hx : FIp_SemanticValues.Canon x) (hy : FIp_SemanticValues.Canon y)
    (run : (FIp_Install.configuration err c r).boundaries.mul x y=ok z) :
    FIp_SemanticValues.Canon z ∧ FIp_SemanticValues.decode z=FIp_SemanticValues.decode x*FIp_SemanticValues.decode y :=
  FIp_SemanticValues.mul x y z hx hy run

#print axioms first_fold
#print axioms dots
#print axioms compared
#print axioms semantic_add
#print axioms semantic_mul
end AspisR1.FIp_InstalledLaws
end
