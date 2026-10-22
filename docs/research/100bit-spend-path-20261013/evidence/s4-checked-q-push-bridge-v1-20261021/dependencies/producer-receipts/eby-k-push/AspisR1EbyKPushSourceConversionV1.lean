import AspisR1EbyKPushExplicitOpsV1
import AspisR1EbyKPushWideToQ
open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1EbyKPushSourceConversionV1

open AspisR1EbyKPushExplicitOpsV1
abbrev Wide := AspisR1EbyKPushExplicitOpsV1.Wide
abbrev Q := AspisR1EbyKPushExplicitOpsV1.Q
abbrev Qm := AspisR1EbyKPushExplicitOpsV1.Qm
abbrev Dot := AspisR1EbyKPushExplicitOpsV1.Dot
abbrev State := AspisR1EbyKPushExplicitOpsV1.State

def pushWithSourceConversion
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (value : Wide) (scalar : Qm) :
    Result ((core.result.Result Unit Unit) × State) :=
  pushWithOps AspisR1EbyKPushWideToQ.fromWide checkedQ pushDot addUsize
    self value scalar

theorem push_source_conversion_success_shape
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (h : pushWithSourceConversion checkedQ pushDot addUsize self value scalar =
      .ok (.Ok (), out)) :
    ∃ a x0 x1 r val d0 d1 i,
      AspisR1EbyKPushWideToQ.fromWide value = .ok a ∧
      a = AspisR1EbyKPushWideToQ.pairFromCoords
        value.c0.c0.a value.c0.c0.b value.c0.c1.a value.c0.c1.b
        value.c1.c0.a value.c1.c0.b value.c1.c1.a value.c1.c1.b ∧
      Array.index_usize a 0#usize = .ok x0 ∧
      Array.index_usize a 1#usize = .ok x1 ∧
      checkedQ scalar = .ok r ∧
      core.result.Result.Insts.CoreOpsTry.branch r = .ok (.Continue val) ∧
      pushDot self.c0 x0 val = .ok d0 ∧
      pushDot self.c1 x1 val = .ok d1 ∧
      addUsize self.count 1#usize = .ok i ∧
      out = { c0 := d0, c1 := d1, count := i } := by
  have hs := push_success_state_shape AspisR1EbyKPushWideToQ.fromWide
    checkedQ pushDot addUsize self value scalar out (by simpa [pushWithSourceConversion] using h)
  rcases hs with ⟨a,x0,x1,r,val,d0,d1,i,ha,hx0,hx1,hr,hbranch,hd0,hd1,hi,hout⟩
  have hcoord := AspisR1EbyKPushWideToQ.fromWide_coordinates value
  have heq : Result.ok a = Result.ok
      (AspisR1EbyKPushWideToQ.pairFromCoords
        value.c0.c0.a value.c0.c0.b value.c0.c1.a value.c0.c1.b
        value.c1.c0.a value.c1.c0.b value.c1.c1.a value.c1.c1.b) :=
    ha.symm.trans hcoord
  cases heq
  exact ⟨AspisR1EbyKPushWideToQ.pairFromCoords
    value.c0.c0.a value.c0.c0.b value.c0.c1.a value.c0.c1.b
    value.c1.c0.a value.c1.c0.b value.c1.c1.a value.c1.c1.b,
    x0,x1,r,val,d0,d1,i,ha,rfl,hx0,hx1,hr,hbranch,hd0,hd1,hi,hout⟩

def pushWithSourceCheckedAdd
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) :
    Result ((core.result.Result Unit Unit) × State) :=
  pushWithSourceConversion checkedQ pushDot UScalar.add self value scalar

theorem push_source_count_increment
    (checkedQ : Qm → Result (core.result.Result Q Unit))
    (pushDot : Dot → Q → Q → Result Dot)
    (self : State) (value : Wide) (scalar : Qm) (out : State)
    (h : pushWithSourceCheckedAdd checkedQ pushDot self value scalar =
      .ok (.Ok (), out)) :
    self.count < maxTerms ∧ out.count.val = self.count.val + 1 := by
  have hsource := push_source_conversion_success_shape checkedQ pushDot
    UScalar.add self value scalar out (by
      simpa [pushWithSourceCheckedAdd] using h)
  rcases hsource with ⟨a,x0,x1,r,val,d0,d1,i,ha,hcoords,hx0,hx1,hr,hbranch,
    hd0,hd1,hi,hout⟩
  have hbelow := push_success_below_bound AspisR1EbyKPushWideToQ.fromWide
    checkedQ pushDot UScalar.add self value scalar out (by
      simpa [pushWithSourceCheckedAdd, pushWithSourceConversion] using h)
  have he := UScalar.add_equiv self.count 1#usize
  have hsame : (self.count + 1#usize : Result Usize) =
      UScalar.add self.count 1#usize := rfl
  rw [hsame] at he
  rw [hi] at he
  have hcount : out.count = i := by
    have hproj := congrArg (fun s : State => s.count) hout
    simpa using hproj
  constructor
  · exact hbelow
  · rw [hcount]
    exact he.2.1

#print axioms push_source_conversion_success_shape
#print axioms push_source_count_increment
end AspisR1EbyKPushSourceConversionV1
