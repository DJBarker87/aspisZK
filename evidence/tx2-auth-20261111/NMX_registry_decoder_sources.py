from pathlib import Path
import re
E=Path(__file__).resolve().parent;s=(E/'NMX_R3_RegistryScriptParts.lean').read_text()
parts={re.search(r'script(\d+)',p)[1]:p for p in re.split(r'(?=def script)',s)[1:]}
for number in ['016','012','008','003']:
 p=parts[number];head,body=p.split(' := do',1);head=head[:head.rindex(' : Program')]
 fields=re.findall(r'\((\w+) :',head);args=' '.join(fields)
 op,var=re.search(r'← scalar \(ops\.(op\d+) (\w+)\)',body).groups()
 inst=re.search(r'map_err (\S+) ',body)[1]
 binder,nextnumber,nextargs=re.search(r'\(fun (\w+) => do\s+script(\d+) ([^\n]+)',body).groups()
 nextargs=nextargs.removesuffix(')')
 nextprog='(fun '+binder+' => NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+')'
 nexteval='(fun '+binder+' => eval (NMX_R3_RegistryScriptParts.script'+nextnumber+' '+nextargs+'))'
 out='''import NMX_R3_RegistryProtocols
import NMX_R3_RegistryDecoderLaw
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDecoder%s
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
'''%number+head.replace('def script'+number,'theorem source')+' :\n eval (NMX_R3_RegistryScriptParts.script'+number+' '+args+') =\n RSL.Spec.bind (scalarSpec (ops.'+op+' '+var+')) (NMX_R3_RegistryDecoderLaw.next '+nexteval+') := by\n'
 out+=' simp only [NMX_R3_RegistryScriptParts.script'+number+',eval_bind,eval_scalar]\n'
 out+=' apply congrArg (RSL.Spec.bind (scalarSpec (ops.'+op+' '+var+')))\n funext r\n'
 out+=' change eval (NMX_R3_RegistryProtocols.formatTail '+inst+' () r '+nextprog+') = _\n'
 out+=' cases r with\n'
 for ctor,val in [('Ok','a'),('Err','e')]:
  out+=' | '+ctor+' '+val+' =>\n  exact NMX_R3_RegistryProtocols.eval_format\n    '+inst+' () (fun _ => rfl) (.'+ctor+' '+val+') '+nextprog+'\n'
 out+='#print axioms source\nend NMX_R3_RegistryDecoder'+number+'\nend\n'
 (E/('NMX_R3_RegistryDecoder'+number+'.lean')).write_text(out)
