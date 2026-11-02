"""Install stateful capacity and runtime operator frames into publication.
This proves partial source transport; native heap/layout/drop adequacy OPEN.
"""
from pathlib import Path
import re,json,hashlib,sys
E=Path('evidence/pv-evh8-20261101');p=Path('lean/PV_EVH_RuntimePublishCompact.lean');s=p.read_text()
cb=s.split('structure Callees where\n')[1].split('\nstructure Compatible')[0];vb=s.split('structure Compatible (c : Callees) : Prop where\n')[1].split('\ndef run')[0]
fields=dict(re.findall(r'(?ms)^  (\w+) : (.*?)(?=^  \w+ : |\Z)',cb));views=dict(re.findall(r'(?ms)^  (\w+) : (.*?)(?=^  \w+ : |\Z)',vb));special={'op12_OPEN','withCapacity_OPEN'}
out='''import PV_EVH_RuntimePublishCompact
import PV_EVH_CapacityWorld
import PV_EVH_RuntimeOperators
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RuntimePublishInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
open PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)
variable [ExternalTypes] [ExternalFuns]
/- Partial source transport, including runtime-fault worlds. LayoutFamily,
allocator/native heap ownership and initialized-region/drop/encoding fidelity
are separate P obligations; this does not discharge them. -/
structure Leaves where
'''
for k,v in fields.items():
 if k not in special:out+='  '+k+' : '+v.rstrip()+'\n'
out+='\nstructure Compatible (c : Leaves) : Prop where\n'
for k,v in views.items():
 if k.replace('_fixed','_OPEN') not in special:out+='  '+k+' : '+v.rstrip()+'\n'
params='''(c : Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent)'''
out+='\ndef install '+params+' : PV_EVH_RuntimePublishCompact.Callees where\n'
for k in fields:
 value='PV_EVH_RuntimeOperators.mapErr frames' if k=='op12_OPEN' else 'fun T n => PV_EVH_CapacityWorld.withCapacity allocator encode (element T).size (element T).align maxBytes owner overflowDiagnostics oomDiagnostics T n' if k=='withCapacity_OPEN' else 'c.'+k
 out+='  '+k+' := '+value+'\n'
out+='\ntheorem install_view '+params+'''
    (hc : Compatible c) (hf : PV_EVH_RuntimeOperators.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_RuntimePublishCompact.Compatible
      (install c frames allocator encode element maxBytes owner overflowDiagnostics oomDiagnostics) where
'''
for k in views:
 value='fun inst r closure => PV_EVH_RuntimeOperators.mapErr_view _ selected frames hf inst r closure' if k=='op12_fixed' else 'fun T n => PV_EVH_CapacityWorld.capacity_view allocator encode (element T).size (element T).align maxBytes owner overflowDiagnostics oomDiagnostics T n' if k=='withCapacity_fixed' else 'hc.'+k
 out+='  '+k+' := '+value+'\n'
out+='\n#print axioms install_view\nend PV_EVH_RuntimePublishInstall\n';q=Path('lean/PV_EVH_RuntimePublishInstall.lean');r=E/'runtime-publish-install-generation.json';record=json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),status='stateful runtime capacity/operator installation; native heap/layout/drop/encoding association OPEN',rows_removed=[]),indent=2)+'\n'
if '--check' in sys.argv:assert q.read_text()==out and r.read_text()==record
else:q.write_text(out);r.write_text(record)
print('Generated stateful capacity/operator publication adapter; native adequacy OPEN')
