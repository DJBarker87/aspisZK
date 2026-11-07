import NNH_AuthReservation
set_option autoImplicit false
noncomputable section
namespace NNH_ReservationOkBinding
open Aeneas Aeneas.Std AspisR1 NNH_Libraries

theorem source (env : RSL.Env) (actual : NP6_StdModel.Reservation)
 (representation : NJC_FilledClause.reserved actual=env.reservation)
 (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 V0 (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ())) :
 actual=.Ok () ∧ actual=LIBB_Tx2Reservation.reservation env := by
 have flag:=NNH_AuthReservation.source env pub proof ck domain success
 have actualOk : actual=.Ok () := by
  cases actual with
  | Ok unit => cases unit; rfl
  | Err error =>
   change false=env.reservation at representation
   rw [flag] at representation
   cases representation
 refine ⟨actualOk,?_⟩
 rw [actualOk]
 unfold LIBB_Tx2Reservation.reservation
 rw [flag]
 rfl
#print axioms source
end NNH_ReservationOkBinding
