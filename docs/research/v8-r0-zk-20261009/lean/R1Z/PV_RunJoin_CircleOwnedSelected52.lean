import R1Z.PV_RunJoin_CircleOwnedComplete52
import R1Z.PV_RunJoin_CircleNeutralSelected52
import R1Z.PV_AL_CircleSelected
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleOwnedSelected52
open ProverRwFull

theorem point (p : PV_RunJoin_CircleOwnedCarrier52.Point) :
    PV_AL_CircleCarriers.decodePoint (PV_RunJoin_CircleOwnedCarrier52.encPoint p) =
      PV_RunJoin_CircleNeutralSelected52.point p := rfl

theorem source [ExternalTypes] (ops : ExternalFuns) (b : Array U8 32#usize)
    (r : aspis_core.r0_transcript.CircleRow) :
    (PV_AL_CircleSelected.selected ops).op259 b r =
      (PV_RunJoin_CircleNeutralSelected52.selected ops).op259 b r := by
  change (do
      let p ← PV_AL_CircleOwned.circle_owned b (PV_AL_CircleCarriers.encodeRow r)
      ok (PV_AL_CircleCarriers.decodePoint p)) = (do
      let p ← PV_RunJoin_CircleRawMap52.circle_owned b (PV_RunJoin_CircleNeutralSelected52.row r)
      ok (PV_RunJoin_CircleNeutralSelected52.point p))
  have hr : PV_AL_CircleCarriers.encodeRow r =
      PV_RunJoin_CircleOwnedComplete52.encRow (PV_RunJoin_CircleNeutralSelected52.row r) := by
    cases r <;> rfl
  rw [hr,PV_RunJoin_CircleOwnedComplete52.complete]
  simp only [bind_assoc_eq,bind_tc_ok,point]

#print axioms point
#print axioms source
end R1Z.PV_RunJoin_CircleOwnedSelected52
