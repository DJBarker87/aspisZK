import R1Z.PV_RunJoin_CircleR72Op3952
import R1Z.PV_RunJoin_CircleMapCanonical54
import R1Z.PV_RunJoin_CircleMapSource54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72MapAdapter54
open PV_RunJoin_CircleR72Carrier52

theorem complete (a : Q) (ha : PV_RunJoin_CircleNeutralShape53.QC a) :
    AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (encQ a)=
      (do let r ← PV_RunJoin_CircleRawMap52.map_parameter a;ok (encOutcome r)) := by
  rw [PV_RunJoin_CircleR72Ops52.op39,PV_RunJoin_CircleMapSource54.complete,
    ← PV_RunJoin_CircleMapCanonical54.complete a ha]
#print axioms complete
end R1Z.PV_RunJoin_CircleR72MapAdapter54
