import JHf_ReferenceFixed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_InstalledValidation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
open _root_.AdapterRw

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) (slot : U64)
    (authenticated : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (authentication : r1_pool_adapter.owned.authenticate_asq8_accounts
      (sdk (JHf_Configuration.value c err)) CPH_Program.verifier
      (JHb_World.e2.second secondSizes) JHb_Programs.pool 3#u8 slot=ok (.Ok authenticated))
    (reconstruction : (sdk (JHf_Configuration.value c err)).op52 JHd_RequestCarrier.actual authenticated
      JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value)) :
    r1_pool_adapter.owned.validate_asq8 (sdk (JHf_Configuration.value c err)) CPH_Program.verifier
      (JHb_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value) := by
  have source:=JHd_Validation.source (sdk (JHf_Configuration.value c err)) slot authenticated
  rw [JHf_ReferenceFixed.source] at source
  exact source authentication (JHf_Configuration.scan c err) reconstruction
#print axioms source
end AspisR1.JHf_InstalledValidation
end
