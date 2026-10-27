import JHf_ReconstructionConfiguration
import JHf_ValidationInversion
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_ValidationRefutation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
open _root_.AdapterRw

/-- A necessary decoded-field/copy law on reached authentication returns.
It asserts no acceptance, output equality or successful child execution. -/
def Faithful (ops : Ops) (verifier : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) : Prop :=
  ∀ pool lane current authenticated,
    r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane current=
      ok (.Ok authenticated) → authenticated.live_snapshot.deployment_domain=JHf_DomainBytes.master

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (slot : core.result.Result U64 solana_program_error.ProgramError)
    (faithful : Faithful (sdk (JHf_ReconstructionConfiguration.value c err)) CPH_Program.verifier
      (JHb_World.e2.second secondSizes)) :
    ¬∃ out,r1_pool_adapter.owned.validate_asq8 (sdk (JHf_ReconstructionConfiguration.value c err))
      CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_DataRequest.value slot=ok (.Ok out) := by
  rintro ⟨out,run⟩
  obtain ⟨request,authenticated,candidate,pool,lane,current,decoded,auth,reconstructed⟩:=
    JHf_ValidationInversion.source _ _ _ _ _ out run
  have same : request=JHd_RequestCarrier.actual :=
    core.result.Result.Ok.inj (Result.ok.inj (decoded.symm.trans (JHf_ReconstructionConfiguration.decoder c err)))
  subst request
  rw [JHf_ReconstructionConfiguration.slot] at reconstructed
  exact JHf_ReconstructionSlot.no_success authenticated candidate
    (faithful pool lane current authenticated auth) ⟨out.statement,reconstructed⟩
#print axioms source
end AspisR1.JHf_ValidationRefutation
end
