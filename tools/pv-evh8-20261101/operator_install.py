"""Generate non-operator leaves and eventful operator installation adapters."""
from pathlib import Path
import re,json,hashlib,sys
E=Path('evidence/pv-evh8-20261101');names=['MaterialFromEntropy','ApplyMaterial','PrivateSalts','PrepareOpening','PublishCompact','PrivateSaltStep']
out='import PV_EVH_OperatorFrames\n'+''.join('import PV_EVH_Op'+n+'\n' for n in names)+'''set_option autoImplicit false
noncomputable section
namespace PV_EVH_OperatorInstall
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Source transport only. Native invocation/drop and actual dictionary selection
remain explicit obligations. No successful execution or trace closure follows. -/
'''
pins=[]
for n in names:
 m='PV_EVH_Op'+n;p=Path('lean/'+m+'.lean');s=p.read_text()
 cb=s.split('structure Callees where\n')[1].split('\nstructure Compatible')[0]
 vb=s.split('structure Compatible (c : Callees) : Prop where\n')[1].split('\ndef run')[0]
 fields=dict(re.findall(r'(?ms)^  (\w+) : (.*?)(?=^  \w+ : |\Z)',cb))
 views=dict(re.findall(r'(?ms)^  (\w+) : (.*?)(?=^  \w+ : |\Z)',vb))
 ops={k for k in fields if k in ['op11_OPEN','op12_OPEN']};assert ops
 out+='\nnamespace '+n+'\nstructure Leaves where\n'
 for k,v in fields.items():
  if k not in ops:out+='  '+k+' : '+v.rstrip()+'\n'
 out+='\nstructure Compatible (c : Leaves) : Prop where\n'
 for k,v in views.items():
  if k.replace('_fixed','_OPEN') not in ops:out+='  '+k+' : '+v.rstrip()+'\n'
 out+='\ndef install (c : Leaves) (frames : PV_EVH_OperatorFrames.Frames) : '+m+'.Callees where\n'
 for k in fields:
  out+='  '+k+' := '+('PV_EVH_OperatorFrames.'+('map' if k=='op11_OPEN' else 'mapErr')+' frames' if k in ops else 'c.'+k)+'\n'
 out+='\ntheorem install_fixed (c : Leaves) (hc : Compatible c)\n    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)\n    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :\n    '+m+'.Compatible (install c frames) where\n'
 for k in views:
  op=k.replace('_fixed','_OPEN')
  out+='  '+k+' := '+('fun inst r closure => PV_EVH_OperatorFrames.'+('map_fixed' if op=='op11_OPEN' else 'mapErr_fixed')+' _ selected frames hf inst r closure' if op in ops else 'hc.'+k)+'\n'
 out+='\n#print axioms install_fixed\nend '+n+'\n'
 pins.append(dict(module=m,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),operators=sorted(ops)))
out+='end PV_EVH_OperatorInstall\n';q=Path('lean/PV_EVH_OperatorInstall.lean');r=E/'operator-install-generation.json';record=json.dumps(dict(inputs=pins,output_sha256=hashlib.sha256(out.encode()).hexdigest(),native_status='OPEN actual selection, invocation/drop and runtime adequacy',rows_removed=[]),indent=2)+'\n'
if '--check' in sys.argv:assert q.read_text()==out and r.read_text()==record
else:q.write_text(out);r.write_text(record)
print('Operator installation adapters:',len(names),'source spines; native adequacy OPEN')
