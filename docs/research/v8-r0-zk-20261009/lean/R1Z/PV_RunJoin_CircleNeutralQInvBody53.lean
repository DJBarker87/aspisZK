import R1Z.PV_RunJoin_CircleNeutralQInvTail53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQInvBody53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53
abbrev C := U32 × U32
abbrev Q := C × C
attribute [local irreducible] PV_RunJoin_CircleRawTower52.field.CM31.mul PV_RunJoin_CircleRawTower52.field.CM31.neg PV_RunJoin_CircleRawTower52.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.square PV_RunJoin_CircleRawTower52.field.CM31.sub PV_RunJoin_CircleR72Raw52.field.CM31.mul PV_RunJoin_CircleR72Raw52.field.CM31.neg PV_RunJoin_CircleR72Raw52.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.square PV_RunJoin_CircleR72Raw52.field.CM31.sub
def owned (a : Q) : Result (Option Q) := do
  let s0 ← PV_RunJoin_CircleRawTower52.field.CM31.square a.1
  let s1 ← PV_RunJoin_CircleRawTower52.field.CM31.square a.2
  let r ← PV_RunJoin_CircleRawTower52.field.mul_by_r s1
  let norm ← PV_RunJoin_CircleRawTower52.field.CM31.sub s0 r
  let v ← PV_RunJoin_CircleRawTower52.field.CM31.inv norm
  PV_RunJoin_CircleNeutralQInvTail53.owned a v
def model (a : Q) : Result (Option Q) := do
  let s0 ← PV_RunJoin_CircleR72Raw52.field.CM31.square a.1
  let s1 ← PV_RunJoin_CircleR72Raw52.field.CM31.square a.2
  let r ← PV_RunJoin_CircleR72Raw52.field.mul_by_r s1
  let norm ← PV_RunJoin_CircleR72Raw52.field.CM31.sub s0 r
  let v ← PV_RunJoin_CircleR72Raw52.field.CM31.inv norm
  PV_RunJoin_CircleNeutralQInvTail53.model a v
theorem complete (a : Q) (ha : QC a) :
    Aligned PV_RunJoin_CircleNeutralQInvTail53.Valid (owned a) (model a) := by
  obtain ⟨s0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.1 ha.1
  obtain ⟨s1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.2 ha.2
  obtain ⟨r,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralRMul53.complete s1 hc1
  obtain ⟨norm,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralCSub53.complete s0 r hc0 hc2
  simp only [owned,model,h0,h0',h1,h1',h2,h2',h3,h3',bind_tc_ok]
  exact PV_RunJoin_CircleNeutralResult53.bind (PV_RunJoin_CircleNeutralCInv53.complete norm hc3)
    (fun v hv => PV_RunJoin_CircleNeutralQInvTail53.complete a v ha hv)

#print axioms owned
#print axioms model
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralQInvBody53
