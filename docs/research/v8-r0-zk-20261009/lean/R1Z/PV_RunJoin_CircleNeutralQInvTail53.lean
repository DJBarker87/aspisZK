import R1Z.PV_RunJoin_CircleNeutralCInv53
import R1Z.PV_RunJoin_CircleNeutralCSquare53
import R1Z.PV_RunJoin_CircleNeutralRMul53
import R1Z.PV_RunJoin_CircleNeutralCSub53
import R1Z.PV_RunJoin_CircleNeutralCMul53
import R1Z.PV_RunJoin_CircleNeutralCNeg53
import R1Z.PV_RunJoin_CircleNeutralZeroResult53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQInvTail53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53
abbrev C := U32 × U32
abbrev Q := C × C
attribute [local irreducible] PV_RunJoin_CircleRawTower52.field.CM31.mul PV_RunJoin_CircleRawTower52.field.CM31.neg PV_RunJoin_CircleRawTower52.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.square PV_RunJoin_CircleRawTower52.field.CM31.sub PV_RunJoin_CircleR72Raw52.field.CM31.mul PV_RunJoin_CircleR72Raw52.field.CM31.neg PV_RunJoin_CircleR72Raw52.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.square PV_RunJoin_CircleR72Raw52.field.CM31.sub
def Valid (x : Option Q) : Prop := ∀ q, x=some q → QC q
def owned (a : Q) (v : C) : Result (Option Q) := do
  let y0 ← PV_RunJoin_CircleRawTower52.field.CM31.mul a.1 v
  let neg ← PV_RunJoin_CircleRawTower52.field.CM31.neg a.2
  let y1 ← PV_RunJoin_CircleRawTower52.field.CM31.mul neg v
  ok (some (y0,y1))
def model (a : Q) (v : C) : Result (Option Q) := do
  let y0 ← PV_RunJoin_CircleR72Raw52.field.CM31.mul a.1 v
  let neg ← PV_RunJoin_CircleR72Raw52.field.CM31.neg a.2
  let y1 ← PV_RunJoin_CircleR72Raw52.field.CM31.mul neg v
  ok (some (y0,y1))
theorem complete (a : Q) (v : C) (ha : QC a) (hv : CC v) :
    Aligned Valid (owned a v) (model a v) := by
  obtain ⟨y0,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralCMul53.complete a.1 v ha.1 hv
  obtain ⟨neg,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralCNeg53.complete a.2 ha.2
  obtain ⟨y1,h6,h6',hc6⟩ := PV_RunJoin_CircleNeutralCMul53.complete neg v hc5 hv
  apply returned _ _ _ (some (y0,y1))
  · simp only [owned,h4,h5,h6,bind_tc_ok]
  · simp only [model,h4',h5',h6',bind_tc_ok]
  · intro q hq
    cases hq
    exact ⟨hc4,hc6⟩

#print axioms Valid
#print axioms owned
#print axioms model
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQInvTail53
