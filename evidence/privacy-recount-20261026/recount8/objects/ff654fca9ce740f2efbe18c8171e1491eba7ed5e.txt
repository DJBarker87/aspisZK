import R1Z.PV_RunJoin_WideArithmetic44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WideUnique44
open ProverCommitWideOps48

theorem unique (x y : Raw) (hx : canonical x) (hy : canonical y)
    (h : value x = value y) : x = y := by
  apply Prod.ext
  · exact (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff x.1 y.1 hx.1 hy.1).mp
      (congrArg QuadraticAlgebra.re h)
  · exact (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff x.2 y.2 hx.2 hy.2).mp
      (congrArg QuadraticAlgebra.im h)
#print axioms unique
end R1Z.PV_RunJoin_WideUnique44
