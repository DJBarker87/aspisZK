import R1Z.PV_RunJoin_CircleMapPrograms54
import R1Z.PV_RunJoin_CircleNeutralQSquare53
import R1Z.PV_RunJoin_CircleNeutralQAdd53
import R1Z.PV_RunJoin_CircleNeutralQSub53
import R1Z.PV_RunJoin_CircleNeutralQInv53
import R1Z.PV_RunJoin_CircleNeutralQMul54
import R1Z.PV_RunJoin_CircleNeutralZeroResult53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleMapCanonical54
open PV_RunJoin_CircleNeutralShape53
abbrev Q := (U32 × U32) × (U32 × U32)

theorem complete (a : Q) (ha : QC a) :
    PV_RunJoin_CircleRawMap52.map_parameter a=PV_RunJoin_CircleMapPrograms54.run a := by
  obtain ⟨s,hs,hs',hcs⟩ := PV_RunJoin_CircleNeutralQSquare53.complete a ha
  obtain ⟨q,hq,hq',hcq⟩ := PV_RunJoin_CircleNeutralQAdd53.complete _ s qone hcs
  have hinv := PV_RunJoin_CircleNeutralQInv53.complete q hcq
  unfold PV_RunJoin_CircleRawMap52.map_parameter PV_RunJoin_CircleMapPrograms54.run
  simp only [hs,hs',hq,hq',bind_tc_ok]
  rw [← hinv.1]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro inverse hi
  cases inverse with
  | none => rfl
  | some inv =>
    have hci : QC inv := hinv.2 (some inv) hi inv rfl
    obtain ⟨num,hn,hn',hcn⟩ := PV_RunJoin_CircleNeutralQSub53.complete _ s qone hcs
    obtain ⟨x,hx,hx',hcx⟩ := PV_RunJoin_CircleNeutralQMul54.complete num inv hcn hci
    obtain ⟨dbl,hd,hd',hcd⟩ := PV_RunJoin_CircleNeutralQAdd53.complete a a ha ha
    obtain ⟨y,hy,hy',hcy⟩ := PV_RunJoin_CircleNeutralQMul54.complete dbl inv hcd hci
    simp only [hn,hn',hx,hx',hd,hd',hy,hy',bind_tc_ok]
    have heq : PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq a.2
        PV_RunJoin_CircleRawTower52.field.CM31.ZERO=
      PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq a.2
        PV_RunJoin_CircleR72Raw52.field.CM31.ZERO := by
      unfold PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
        PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
      rw [PV_RunJoin_CircleNeutralZeroResult53.meq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro b _
      cases b with
      | false => rfl
      | true => exact PV_RunJoin_CircleNeutralZeroResult53.meq _ _
    rw [heq]
#print axioms complete
end R1Z.PV_RunJoin_CircleMapCanonical54
