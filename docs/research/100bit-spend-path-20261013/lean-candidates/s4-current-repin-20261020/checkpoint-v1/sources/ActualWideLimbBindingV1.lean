import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1EbyKPushWideToQ
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCurrentWideBinding
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
def withCurrentWideToLimbs (ops : Ops) : Ops :=
  { ops with wideToLimbs := AspisR1EbyKPushWideToQ.toLimbs }
theorem wideToLimbs_binding (ops : Ops) (x : Wide) :
    (withCurrentWideToLimbs ops).wideToLimbs x = AspisR1EbyKPushWideToQ.toLimbs x := rfl
theorem toLimbs_coordinates (x : AspisR1EbyKPushWideToQ.Wide) :
    AspisR1EbyKPushWideToQ.toLimbs x = .ok (Array.make 8#usize
      [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
       x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]) := by
  simp [AspisR1EbyKPushWideToQ.toLimbs, Array.make]
#print axioms wideToLimbs_binding
#print axioms toLimbs_coordinates
end AspisR1FastDotsCurrentWideBinding
