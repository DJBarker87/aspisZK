import FJs_PointTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_CircleTransport
open AspisCircleTensorBinding
variable {K E : Type} [Field K] [Field E] [NeZero (2:K)] [NeZero (2:E)]

theorem doubled (h : K →+* E) (x : K) (n : Nat) :
    h (doubledFactor x n)=doubledFactor (h x) n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [doubledFactor,map_sub,map_mul,map_ofNat,map_pow,map_one,ih]

theorem line (h : K →+* E) (x : K) (n : Nat) :
    h (naturalLineValue x n)=naturalLineValue (h x) n := by
  simp only [naturalLineValue,map_prod,doubled]

theorem circle (h : K →+* E) (x y : K) (j : Nat) :
    h (SelectedCircleWeightModel.circleWeight x y j)=
      SelectedCircleWeightModel.circleWeight (h x) (h y) j := by
  unfold SelectedCircleWeightModel.circleWeight
  rw [map_mul,line]
  split <;> simp only [map_one]

#print axioms doubled
#print axioms line
#print axioms circle
end AspisR1.FJs_CircleTransport
end
