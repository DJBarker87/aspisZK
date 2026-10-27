import JHf_AuthenticationInstalledDomain
import JHf_ValidationPoolInversion
import JHf_RealPool
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_MasterFieldRefutation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
open _root_.AdapterRw

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (slot : S2W_ExtractionBoundary.Slot)
    (field : JHf_AuthenticationInstalledDomain.Field (sdk (JHf_ReconstructionConfiguration.value c err))) :
    ¬∃ out,r1_pool_adapter.owned.validate_asq8 (sdk (JHf_ReconstructionConfiguration.value c err))
      CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_DataRequest.value slot=ok (.Ok out) := by
  rintro ⟨out,run⟩
  obtain ⟨request,authenticated,candidate,pool,lane,current,decoded,poolCall,auth,reconstructed⟩:=
    JHf_ValidationPoolInversion.source _ _ _ _ _ out run
  have same : request=JHd_RequestCarrier.actual :=
    core.result.Result.Ok.inj (Result.ok.inj (decoded.symm.trans (JHf_ReconstructionConfiguration.decoder c err)))
  subst request
  have samePool : pool=JHb_Programs.pool := Result.ok.inj (poolCall.symm.trans (JHf_RealPool.source c err))
  subst pool
  have domain:=JHf_AuthenticationInstalledDomain.source (JHf_ReconstructionConfiguration.seed c)
    err lane current authenticated field auth
  rw [JHf_ReconstructionConfiguration.slot] at reconstructed
  exact JHf_ReconstructionSlot.no_success authenticated candidate domain ⟨out.statement,reconstructed⟩
#print axioms source
end AspisR1.JHf_MasterFieldRefutation
end
