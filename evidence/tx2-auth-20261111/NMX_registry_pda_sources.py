from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NMX_R3_RegistryScriptParts.lean').read_text();a=s.index('def script017');b=s.index('def script016');head=s[a:b].split(' := do')[0];head=head[:head.rindex(' : Program')]
args='(NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot p registry_program val4'
head=head.replace('def script017 (ops : Ops)','theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)')
out='''import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda17
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
'''+head+''' :
 eval (NMX_R3_RegistryScriptParts.script017 '''+args+''') =
 RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.entry1 p val4.bump) registry_program)
  (NMX_R3_RegistryPdaLaw.next (fun q => eval
   (NMX_R3_RegistryScriptParts.script018 (NMX_R3_RegistryOps.install base D env)
    verifier_program entry_account current_slot p val4 q))) := by
 simp only [NMX_R3_RegistryScriptParts.script017,eval_bind,eval_scalar,eval_pda,
  NMX_R3_RegistryScalarOps.as_ref,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]
 apply congrArg (RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.entry1 p val4.bump) registry_program))
 funext r
 change eval (NMX_R3_RegistryProtocols.formatTail
  r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
  () r (fun q => NMX_R3_RegistryScriptParts.script018 (NMX_R3_RegistryOps.install base D env)
   verifier_program entry_account current_slot p val4 q)) = _
 exact NMX_R3_RegistryProtocols.eval_format _ () (fun _ => rfl) r _
#print axioms source
end NMX_R3_RegistryPda17
end
'''
(E/'NMX_R3_RegistryPda17.lean').write_text(out)
