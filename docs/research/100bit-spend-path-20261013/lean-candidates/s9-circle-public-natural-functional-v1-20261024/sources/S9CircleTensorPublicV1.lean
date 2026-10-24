import S9CircleSourceFactorV1
import S9CircleExactTwoV1
import S9ConstructorV3CompleteFactorSemanticsV1
import S9SharedSumObservationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CircleTensorPublicV1
open AspisR1S9FactorTableSemanticsV1 (ExactQM Table)
open AspisR1S9CirclePointscanModelV1 (Point pointRow circleRow)
open AspisR1S9CircleTensorGenericV1 (circleTable)
open AspisR1S9StatementTensorGenericV1 (tensorRow)
open AspisR1S9ConstructorV3CompleteFactorSemanticsV1 (CircleRows Circles)
open AspisR1S9ConstructorV3QMMulSemanticsV1 (decode)
open AspisR1S9SharedSumObservationsV1 (finIndex finIndex_val)
abbrev Q := ExactQM
abbrev M := AspisR1CurrentWide.Proof.MExact

private instance qTwoNeZero : NeZero (2 : Q) :=
  ⟨AspisR1S9CircleExactTwoV1.exact_q_two_ne_zero⟩

/-- Exact bounded read of the SAME actual two constructor circle points. -/
def sourceCircle (z : Circles) (r : Fin 2) : Point :=
  z.val[r.val]'(by rw [z.property];exact r.isLt)

theorem pointRow_sourceCircle (z : Circles) (r : Fin 2) (d i : Nat) :
    pointRow z r.val d i=circleRow (sourceCircle z r) d i := by
  unfold pointRow sourceCircle
  rw [List.getElem?_eq_getElem (by rw [z.property];exact r.isLt)]

/-- One exact source CircleRows factor; the selected point is read from the
SAME z, never supplied as an independently chosen coordinate pair. -/
theorem circle_model_factor (z : Circles) (model : Table) (hc : CircleRows z model)
    (r : Fin 2) (k : Usize) (hkr : k.val=3+r.val) (d : Fin 5) (s : Fin 4) :
    model k.val d.val s.val=
      circleTable (decode (sourceCircle z r).x) (decode (sourceCircle z r).y) d.val s.val := by
  let di := finIndex (by decide : 5≤64) d
  let si := finIndex (by decide : 4≤64) s
  have hd : di.val<5 := by simpa only [di,finIndex_val] using d.isLt
  have hs : si.val<4 := by simpa only [si,finIndex_val] using s.isLt
  have hk3 : 3≤k.val := by omega
  have hk5 : k.val<5 := by have := r.isLt;omega
  have hidx : k.val-3=r.val := by omega
  have h := hc k di si hk3 hk5 hd hs
  simp only [di,si,finIndex_val,hidx] at h
  exact h.trans ((pointRow_sourceCircle z r d.val s.val).trans
    (AspisR1S9CircleSourceFactorV1.source_circle_factor (sourceCircle z r) d.val s.val))

/-- Both source circle rows represent the existing natural-circle basis
weight at the SAME actual constructor input point and symbolic index. -/
theorem circle_tensor_row_eq_circleWeight (z : Circles) (model : Table)
    (hc : CircleRows z model) (r : Fin 2) (k : Usize) (hkr : k.val=3+r.val)
    (j : Fin 1024) :
    tensorRow (model k.val) j=
      AspisR1.SelectedCircleWeightModel.circleWeight
        (decode (sourceCircle z r).x) (decode (sourceCircle z r).y) j.val := by
  have he : tensorRow (model k.val) j=
      tensorRow (circleTable (decode (sourceCircle z r).x) (decode (sourceCircle z r).y)) j := by
    unfold tensorRow
    apply Finset.prod_congr rfl
    intro d _
    exact circle_model_factor z model hc r k hkr d
      ⟨j.val/4^d.val%4,Nat.mod_lt _ (by omega)⟩
  exact he.trans (AspisR1S9CircleTensorGenericV1.circle_tensor_eq_circleWeight
    (decode (sourceCircle z r).x) (decode (sourceCircle z r).y) j)

#print axioms pointRow_sourceCircle
#print axioms circle_model_factor
#print axioms circle_tensor_row_eq_circleWeight
end AspisR1S9CircleTensorPublicV1
