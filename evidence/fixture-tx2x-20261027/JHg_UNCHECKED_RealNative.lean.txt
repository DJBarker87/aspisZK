import JHg_RealSuffix
import JHg_InstalledValidation
import JHf_KeyFixed
import JHf_EmissionAssociation
import JHb_RequestCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_RealNative
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

def native {C : Type} (c : Configuration FIo_Install.W C) (err : C) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk (JHf_Configuration.value c err))

/-- Conditional source-native result; both uncomputed authentication and
reconstruction children stay visible. This is not unconditional accepted2. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) (slot : U64)
    (authenticated : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (authentication : AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
      (sdk (JHf_Configuration.value c err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) JHb_Programs.pool 3#u8 slot=ok (.Ok authenticated))
    (reconstruction : (sdk (JHf_Configuration.value c err)).op52 JHd_RequestCarrier.actual authenticated
      JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value))
    (JGz_Realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    native c err CPH_Program.verifier (JHg_World.e2.second secondSizes)
      JHb_DataRequest.value (.Ok slot)=ok (.Ok ()) := by
  have magic:=JHb_RequestCarrier.magic (sdk (JHf_Configuration.value c err))
  rw [JHf_KeyFixed.source] at magic
  have validated:=JHg_InstalledValidation.source c err slot authenticated authentication reconstruction
  have prefix:=JGx_SdkAfterValidationEq.source (sdk (JHf_Configuration.value c err))
    CPH_Program.verifier (JHg_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)
    JGx_Validated.value (JGx_EntryReads.count _) magic validated
  exact prefix.trans ((JHg_RealSuffix.source (JHf_Configuration.select c) err JGz_Realizes).trans
    (JHf_EmissionAssociation.accepted c err))
#print axioms source
end AspisR1.JHg_RealNative
end
