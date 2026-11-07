import NMT_Outcome
import NLV_Deployed
import NLJ_Tx1State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_RowSpec_094
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open NMT_Outcome
abbrev Input := NLJ_Tx1.Input
abbrev World := NLJ_Packets.Frame094
abbrev Out := NLJ_Tx1.Out
abbrev Native := Producer Input Out World SdkC_Source.Query
/-- OWN argument extents, recorded verbatim for328. No endpoint/Result clause. -/
def Domain (i : Input) : Prop :=
 i.proof.val.length=57607 ∧ i.publicBytes.val.length=1880
/-- A total fixed producer must match EVERY Result, every attempted digest in
order and the returned external frame at the SAME original inputs. Private
allocation internals are excluded by(bl)(3); stopped arms have no post-world.
This is a TARGET, not an installed extraction/native interpretation or root. -/
def RowSpec_094 {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native) : Prop :=
 ∀ (i : Input) (before : World), Domain i →
 i.digest=NLV_Deployed.digest missing indexError reservation →
 let cfg:=NLV_Deployed.configuration missing indexError reservation
 matches before
  (SdkC_Source.run i.hashv
   (NGQ_Normalize.normalize (GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
     i.hashv i.digest i.publicValue i.publicBytes i.proof i.k)) [])
  (native i before)
theorem complete {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native)
 (packet : RowSpec_094 missing indexError reservation native)
 (i : Input) (before : World) (domain : Domain i)
 (digest : i.digest=NLV_Deployed.digest missing indexError reservation) :
 let cfg:=NLV_Deployed.configuration missing indexError reservation
 let expected:=SdkC_Source.run i.hashv
  (NGQ_Normalize.normalize (GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
    i.hashv i.digest i.publicValue i.publicBytes i.proof i.k)) []
 result (native i before).exit=expected.1 ∧
 (native i before).attempted=expected.2 ∧ frame before (native i before).exit :=
 packet i before domain digest
#print RowSpec_094
#print axioms complete
end AspisR1.NMT_RowSpec_094
