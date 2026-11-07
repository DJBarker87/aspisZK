from pathlib import Path
import re
E=Path(__file__).resolve().parent;s=(E/'NMX_R3_RegistryScriptParts.lean').read_text()
parts={re.search(r'script(\d+)',p)[1]:p for p in re.split(r'(?=def script)',s)[1:]}
for number,seed in [('009','entry2 p val5.bump'),('013','registry1 master_account.key val1.bump'),('004','registry2 master_account.key val1.bump')]:
 p=parts[number];head,body=p.split(' := do',1);head=head[:head.rindex(' : Program')]
 fields=re.findall(r'\((\w+) :',head);args=' '.join(fields)
 args=args.replace('ops','(NMX_R3_RegistryOps.install base D env)')
 inst=re.search(r'map_err (\S+) ',body)[1]
 binder,nextnumber,nextargs=re.search(r'\(fun (\w+) => do\s+script(\d+) ([^\n]+)',body).groups();nextargs=nextargs.removesuffix(')')
 nextargs=re.sub(r'\bops\b','(NMX_R3_RegistryOps.install base D env)',nextargs)
 if number in ['013','004']:nextargs=re.sub(r'\bp\b','master_account.key',nextargs)
 nextprog='(fun '+binder+' => NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+')'
 nexteval='(fun '+binder+' => eval (NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+'))'
 seeds='(NMX_R3_PdaSeeds.'+seed+')'
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
'''%number+head.replace('def script'+number+' (ops : Ops)','theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)')+' :\n eval (NMX_R3_RegistryScriptParts.script'+number+' '+args+') =\n RSL.Spec.bind (pdaSpec '+seeds+' registry_program) (NMX_R3_RegistryPdaLaw.next '+nexteval+') := by\n'
 out+=' simp only [NMX_R3_RegistryScriptParts.script'+number+',eval_bind,eval_scalar,eval_pda,\n  NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]\n'
 out+=' apply congrArg (RSL.Spec.bind (pdaSpec '+seeds+' registry_program))\n funext r\n'
 out+=' change eval (NMX_R3_RegistryProtocols.formatTail '+inst+' () r '+nextprog+') = _\n'
 out+=' cases r with\n'
 for ctor,val in [('Ok','a'),('Err','e')]:
  out+=' | '+ctor+' '+val+' =>\n  exact NMX_R3_RegistryProtocols.eval_format\n    '+inst+' () (fun _ => rfl) (.'+ctor+' '+val+') '+nextprog+'\n'
 out+='#print axioms source\nend NMX_R3_RegistryPda'+number+'\nend\n'
 (E/('NMX_R3_RegistryPda'+number+'.lean')).write_text(out)
