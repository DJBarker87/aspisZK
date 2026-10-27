import R1Z.PV_Src_RecordRootClosed
set_option autoImplicit false
namespace R1Z.PV_Src_RecordAssociation
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1

/-! The missing installed Records/R_shipped association, stated as a source
call law. No proof of this native interface is assumed or added to T. -/
def Associated (external : ExternalLinear) (records : Records) : Prop :=
  ∀ input out rec chg snapshot asset,
    records.call input out rec chg snapshot asset =
      @PV_Src_RecordDynamic.call external input out rec chg snapshot asset

theorem dictionary (external : ExternalLinear) (records : Records) (h : Associated external records) :
    records = @PV_Src_RecordDynamic.dictionary external := by
  cases records with
  | mk call =>
    change Records.mk call = Records.mk _
    congr 1
    funext input out rec chg snapshot asset
    exact h input out rec chg snapshot asset

#print axioms dictionary
end R1Z.PV_Src_RecordAssociation
