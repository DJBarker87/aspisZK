import R1Z.PV_RunJoin_EnteredCallback
import R1Z.PV_RunJoin_PublicReservation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EnteredGuards
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_Follows PV_RunJoin_LedgerWorld
variable [ExternalTypes]

theorem guarded (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (secret : Secret) (hash : Hash)
    (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : World)
    (empty : s.entered = none) :
    letI : ExternalFuns := ops
    Follows (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered)
      (PV_RunJoin_PublicReservation.guards address secret.mask_nonce context)
      (PV_RunJoin_ReservationGuards.guarded (dictionary ops schedule unix address)
        secret hash binding context s) := by
  letI : ExternalFuns := ops
  unfold PV_RunJoin_PublicReservation.guards PV_RunJoin_ReservationGuards.guarded
  apply bind_common
  intro different
  split
  · simpa only [empty] using returned (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered)
      ((.Err .Layout,s) : PV_RunJoin_ReservationGuards.MaterialStatus × World)
  · apply bind_common
    intro mask
    split
    · simpa only [empty] using returned (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered)
        ((.Err .Layout,s) : PV_RunJoin_ReservationGuards.MaterialStatus × World)
    · apply bind_common
      intro factor
      split
      · simpa only [empty] using returned (fun out : PV_RunJoin_ReservationGuards.MaterialStatus × World => out.2.entered)
          ((.Err .Layout,s) : PV_RunJoin_ReservationGuards.MaterialStatus × World)
      · exact PV_RunJoin_EnteredCallback.entered ops schedule unix address secret hash binding context s

#print axioms guarded
end R1Z.PV_RunJoin_EnteredGuards
