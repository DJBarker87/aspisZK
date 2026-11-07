from pathlib import Path
import re
E=Path(__file__).resolve().parent;s=(E/'NMX_R3_RegistryScriptParts.lean').read_text();parts={re.search(r'script(\d+)',p)[1]:p for p in re.split(r'(?=def script)',s)[1:]}
for number,account,expected,seed in [('005','registry_account','val2','programdata registry_program val1.programdata_bump'),('010','entry_account','val6','programdata verifier_program val5.programdata_bump')]:
 p=parts[number];head,body=p.split(' := do',1);head=head[:head.rindex(' : Program')]
 fields=re.findall(r'\((\w+) :',head);args=' '.join(fields).replace('ops','(NMX_R3_RegistryOps.install base D env)')
 inst=re.search(r'map_err (\S+) ',body)[1];binder,nextnumber,nextargs=re.search(r'\(fun (\w+) => do\s+script(\d+) ([^\n]+)',body).groups();nextargs=nextargs.removesuffix(')');nextargs=re.sub(r'\bops\b','(NMX_R3_RegistryOps.install base D env)',nextargs)
 nextprog='(fun '+binder+' => NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+')';nexteval='(fun '+binder+' => eval (NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+'))';seeds='(NMX_R3_PdaSeeds.'+seed+')';flag='!decide ('+account+'.key = '+expected+')'
 out='''import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_RegistryPure
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda%s
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
'''%number+head.replace('def script'+number+' (ops : Ops)','theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)')+' :\n eval (NMX_R3_RegistryScriptParts.script'+number+' '+args+') =\n (if '+flag+' then RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) else\n RSL.Spec.bind (pdaSpec '+seeds+' loader) (NMX_R3_RegistryPdaLaw.next '+nexteval+')) := by\n'
 out+=' by_cases rejected : ('+flag+') = true\n'
 simp='simp only [NMX_R3_RegistryScriptParts.script'+number+',eval_bind,eval_scalar,eval_pda,eval_if,eval_pure,\n   NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,rejected,↓reduceIte]\n'
 out+=' · '+simp+' · '+simp
 out+='   apply congrArg (RSL.Spec.bind (pdaSpec '+seeds+' loader))\n   funext r\n'
 out+='   change eval (NMX_R3_RegistryProtocols.formatTail '+inst+' () r '+nextprog+') = _\n'
 out+='   cases r with\n'
 for ctor,val in [('Ok','a'),('Err','e')]:out+='   | '+ctor+' '+val+' =>\n    exact NMX_R3_RegistryProtocols.eval_format\n      '+inst+' () (fun _ => rfl) (.'+ctor+' '+val+') '+nextprog+'\n'
 out+='#print axioms source\nend NMX_R3_RegistryPda'+number+'\nend\n';(E/('NMX_R3_RegistryPda'+number+'.lean')).write_text(out)
