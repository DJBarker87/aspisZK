import AspisR1EbyKPushSourceConversionV1
import AspisR1EbyKCheckedQAllParamV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1EbyKPushConcreteCheckedQV1

open AspisR1EbyKPushSourceConversionV1
open AspisR1EbyKPushExplicitOpsV1

abbrev All := AspisR1EbyKCheckedQAllParamV1.IterAll
abbrev limbsOf := AspisR1EbyKCheckedQAllParamV1.limbsOf
abbrev checkedQWithAll := AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
abbrev Q := AspisR1EbyKPushExplicitOpsV1.Q
abbrev Qm := AspisR1EbyKPushExplicitOpsV1.Qm
abbrev Wide := AspisR1EbyKPushExplicitOpsV1.Wide
abbrev Dot := AspisR1EbyKPushExplicitOpsV1.Dot
abbrev State := AspisR1EbyKPushExplicitOpsV1.State

def pushWithConcreteCheckedQ (all : All) (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) :
    Result ((core.result.Result Unit Unit) × State) :=
  pushWithSourceCheckedAdd (checkedQWithAll all) pushDot self value scalar

theorem push_concrete_checked_q_success
    (all : All) (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (h : pushWithConcreteCheckedQ all pushDot self value scalar =
      .ok (.Ok (), out)) :
    ∃ d0 d1 i,
      pushDot self.c0
        (AspisR1EbyKPushWideToQ.qFromCoords value.c0.c0.a value.c0.c0.b
          value.c0.c1.a value.c0.c1.b)
        (Array.make 4#usize [scalar.c0.a, scalar.c0.b, scalar.c1.a, scalar.c1.b]) = .ok d0 ∧
      pushDot self.c1
        (AspisR1EbyKPushWideToQ.qFromCoords value.c1.c0.a value.c1.c0.b
          value.c1.c1.a value.c1.c1.b)
        (Array.make 4#usize [scalar.c0.a, scalar.c0.b, scalar.c1.a, scalar.c1.b]) = .ok d1 ∧
      out = { c0 := d0, c1 := d1, count := i } ∧
      self.count < maxTerms ∧ out.count.val = self.count.val + 1 := by
  have hs := push_source_conversion_success_shape
    (checkedQWithAll all) pushDot UScalar.add self value scalar out (by
      simpa [pushWithConcreteCheckedQ, pushWithSourceCheckedAdd,
        pushWithSourceConversion] using h)
  rcases hs with ⟨a,x0,x1,r,val,d0,d1,i,ha,hcoord,hx0,hx1,hr,hbranch,
    hd0,hd1,hi,hout⟩
  have hc := push_source_count_increment (checkedQWithAll all) pushDot
    self value scalar out (by
      simpa [pushWithConcreteCheckedQ, pushWithSourceCheckedAdd,
        pushWithSourceConversion] using h)
  have hval : val = Array.make 4#usize
      [scalar.c0.a, scalar.c0.b, scalar.c1.a, scalar.c1.b] := by
    cases r with
    | Ok q =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
      subst val
      have hq := AspisR1EbyKCheckedQAllParamV1.checkedQWithAll_success_limbs
        all scalar q hr
      exact hq
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch] at hbranch
  have hx0v : x0 = AspisR1EbyKPushWideToQ.qFromCoords
      value.c0.c0.a value.c0.c0.b value.c0.c1.a value.c0.c1.b := by
    rw [hcoord] at hx0
    simpa [AspisR1EbyKPushWideToQ.pairFromCoords,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.index_usize, Array.make] using
        (Result.ok.inj hx0).symm
  have hx1v : x1 = AspisR1EbyKPushWideToQ.qFromCoords
      value.c1.c0.a value.c1.c0.b value.c1.c1.a value.c1.c1.b := by
    rw [hcoord] at hx1
    simpa [AspisR1EbyKPushWideToQ.pairFromCoords,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.index_usize, Array.make] using
        (Result.ok.inj hx1).symm
  rw [hval, hx0v] at hd0
  rw [hval, hx1v] at hd1
  have hiVal : i.val = self.count.val + 1 := by
    have he := UScalar.add_equiv self.count 1#usize
    have hsame : (self.count + 1#usize : Result Usize) =
        UScalar.add self.count 1#usize := rfl
    rw [hsame, hi] at he
    exact he.2.1
  refine ⟨d0, d1, i, hd0, hd1, hout, hc.1, ?_⟩
  rw [hout]
  exact hiVal

#print axioms push_concrete_checked_q_success
end AspisR1EbyKPushConcreteCheckedQV1
