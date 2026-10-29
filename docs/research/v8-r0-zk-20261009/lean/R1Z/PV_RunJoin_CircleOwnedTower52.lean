import R1Z.PV_RunJoin_CircleOwnedOp2152
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleOwnedTower52
open PV_RunJoin_CircleOwnedCarrier52
/-- Complete option-valued inverse transport, with no canonicality or success premise. -/
theorem inverse (q : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.try_inv (encQ q) = (do
      let x ← PV_RunJoin_CircleRawTower52.field.QM31.try_inv q
      ok (Option.map encQ x)) := PV_RunJoin_CircleOwnedOps52.op21 q
#print axioms inverse
end R1Z.PV_RunJoin_CircleOwnedTower52
