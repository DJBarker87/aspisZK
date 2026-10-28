from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin30-20261028';rows=[]
for kind in ['Transfer','Withdrawal']:
 ns='R1Z.PV_RunJoin_Outer'+kind+'Composed30';text='''import R1Z.PV_RunJoin_OuterInnerPath30
import R1Z.PV_RunJoin_OuterKINDDomain30
import R1Z.PV_RunJoin_OuterKINDErrors30
set_option autoImplicit false
noncomputable section
namespace NS
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]
'''.replace('KIND',kind).replace('NS',ns)
 for errors in [False,True]:
  name='PV_RunJoin_Outer'+kind+('Errors' if errors else 'Domain')+'30';s=(L/(name+'.lean')).read_text()
  start=s.index('def Path\n');end=s.index('\ntheorem ',start);definition=s[start:end]
  if errors:definition=definition.replace('def Path\n','def ErrorPath\n')
  pattern=r'wp \(\n( +)pool_v1.pair_forest_trace.compile_forest_from_copies([\s\S]+?)\n +\) '+(r'\(fun r => r = .Err error\)' if errors else 'isRustOk')
  definition,count=re.subn(pattern,lambda m:'R1Z.PV_RunJoin_OuterInnerPath30.'+('ErrorPath' if errors else 'Path')+m[2]+(' error' if errors else ''),definition)
  assert count==1,(name,count)
  text+='\n'+definition+'\n'
  tstart=s.index('theorem ');header=s[tstart:s.index(' := by',tstart)]
  if errors:header=header.replace('↔ Path public1','↔ ErrorPath public1')
  lemma='error_iff' if errors else 'success_iff';path='ErrorPath' if errors else 'Path';rewrite='error_wp' if errors else 'inner_wp'
  text+='\n'+header+f''' := by
  rw [R1Z.{name}.{lemma}]
  unfold R1Z.{name}.Path {path}
  simp only [R1Z.PV_RunJoin_OuterInnerPath30.{rewrite}]
#print axioms {lemma}
'''
 text+='end '+ns+'\n';p=L/('PV_RunJoin_Outer'+kind+'Composed30.lean')
 if '--check' in sys.argv:assert p.read_text()==text
 else:p.write_text(text)
 rows.append(dict(module=p.stem,sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' not in sys.argv:(E/'composed-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
print('composed domains','checked' if '--check' in sys.argv else 'generated')
