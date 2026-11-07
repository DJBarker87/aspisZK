import RPx_Deployed
import NLJ_Tx1State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Deployed
open Aeneas Aeneas.Std Result
/-- Exactly the headline installation; arbitrary Ops dictionaries are never
parameters of the proposed 094 packet. Uninstalled is a headline parameter. -/
def installed {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) :=
 FIp_Install.configuration indexError (IDa_Deployed.deployedConfiguration missing indexError reservation) reservation
def configuration {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) : NLJ_Tx1.Configuration :=
 let c := installed missing indexError reservation
 ⟨GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry,c.boundaries,c.std⟩
def digest {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) :=
 DrvC_Installation.currentDigest (installed missing indexError reservation)
theorem dictionary {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) :
 NLJ_Tx1.ops (configuration missing indexError reservation) =
 DrvC_Installation.currentInstalled (installed missing indexError reservation) :=
 (DrvC_Installation.current_dictionary (installed missing indexError reservation)).symm
theorem digest_slot {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (parts : Slice (Slice U8)) :
 (digest missing indexError reservation).digest () parts =
 (DrvC_Installation.sdk (installed missing indexError reservation)).op43 () parts := rfl
#print axioms dictionary
#print axioms digest_slot
end AspisR1.NLV_Deployed
end
