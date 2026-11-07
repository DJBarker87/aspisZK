import NMT_Outcome
import NLV_Deployed
import NLV_PreparePacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_RowSpec_087
open Aeneas Aeneas.Std Result AspisR1CurrentCaller AspisR1PublicPreparation
open NMT_Outcome
abbrev Input := NLJ_Prepare.Input Unit
abbrev World := NLR_Interface.ExternalFrame
abbrev Out := NLJ_Prepare.Out
abbrev Event := PreparedHashCode.Event
abbrev Native := Producer Input Out World Event
/-- The public value, proof and scratch are the row's OWN original arguments.
The caller discharges this extent; no child result is a domain predicate. -/
def Domain (i : Input) : Prop := i.proof.val.length=57607
/-- Under (bl)(3), private allocator internals are outside the row. The returned
scratch is IN Out on every returned Rust Result, including Err. A stopped arm
retains the attempted digest prefix and has no post-abort scratch or world. -/
def RowSpec_087 {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native) : Prop :=
 ∀ (i : Input) (before : World), Domain i →
 i.digest=NLV_Deployed.digest missing indexError reservation →
 let cfg:=NLV_PreparePacket.configuration (NLV_Deployed.configuration missing indexError reservation)
 let expected:=PreparedHashCode.run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch)
 Matches before (expected.2,expected.1) (native i before)
/-- Every instantiated packet supplies the COMPLETE Result and ordered log,
not merely its accepted branch. This is specification elimination, not a root. -/
theorem complete {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native)
 (packet : RowSpec_087 missing indexError reservation native)
 (i : Input) (before : World) (domain : Domain i)
 (digest : i.digest=NLV_Deployed.digest missing indexError reservation) :
 let cfg:=NLV_PreparePacket.configuration (NLV_Deployed.configuration missing indexError reservation)
 let expected:=PreparedHashCode.run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch)
 result (native i before).exit=expected.2 ∧
 (native i before).attempted=expected.1 ∧ frame before (native i before).exit :=
 packet i before domain digest
#print RowSpec_087
#print axioms complete
end AspisR1.NMT_RowSpec_087
