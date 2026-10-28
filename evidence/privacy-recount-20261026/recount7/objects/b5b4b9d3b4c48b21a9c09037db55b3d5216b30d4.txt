import R1Z.PV_Src_RecordRootClosed
set_option autoImplicit false
namespace R1Z.PV_Src_RecordRootDictionary
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem source : @PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary =
    PV_Src_RecordReference.withRoots PV_Src_CanonicalRoots.table := by
  change Records.mk _ = Records.mk _
  congr 1
  funext input out rec chg snapshot asset
  exact PV_Src_RecordRootClosed.call input out rec chg snapshot asset

#print axioms source
end R1Z.PV_Src_RecordRootDictionary
