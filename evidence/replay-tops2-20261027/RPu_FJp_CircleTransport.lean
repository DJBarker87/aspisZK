import RPu_FJo_CircleInverses
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_CircleTransport
open AspisWide.FinalEncoder
variable {K : Type} [Field K]
/-- One argument at a time: no normalization of the concrete extension field. -/
theorem alpha (a a' x y : K) (v : Fin 4 → K) (h : a=a') :
    FoldRuntimeAlgebra.circleWithInverses a x y v =
      FoldRuntimeAlgebra.circleWithInverses a' x y v := congrArg (fun z => FoldRuntimeAlgebra.circleWithInverses z x y v) h
theorem x (a x x' y : K) (v : Fin 4 → K) (h : x=x') :
    FoldRuntimeAlgebra.circleWithInverses a x y v =
      FoldRuntimeAlgebra.circleWithInverses a x' y v := congrArg (fun z => FoldRuntimeAlgebra.circleWithInverses a z y v) h
theorem y (a x y y' : K) (v : Fin 4 → K) (h : y=y') :
    FoldRuntimeAlgebra.circleWithInverses a x y v =
      FoldRuntimeAlgebra.circleWithInverses a x y' v := congrArg (fun z => FoldRuntimeAlgebra.circleWithInverses a x z v) h
theorem dots (a x y : K) (v v' : Fin 4 → K) (h : v=v') :
    FoldRuntimeAlgebra.circleWithInverses a x y v =
      FoldRuntimeAlgebra.circleWithInverses a x y v' := congrArg (fun z => FoldRuntimeAlgebra.circleWithInverses a x y z) h
#print axioms alpha
#print axioms x
#print axioms y
#print axioms dots
end AspisR1.FJp_CircleTransport
end
