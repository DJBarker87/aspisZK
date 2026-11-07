"""Generate only structural RSL/AdapterRw carrier maps; no semantic laws fabricated."""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
src=Path('docs/research/100bit-spend-path-20261013/lean/AdapterRwTypes.lean').read_text()
prev='NND_ScalarLaws'
status='''import NND_ScalarLaws
import RSL_Pool
set_option autoImplicit false
namespace NND_Carrier
open AdapterRw.aspis_statement.pool_v1.verifier_registry

def status : VerifierEntryStatusV1 → RSL.EntryStatus
 | .Pending => .pending | .Active => .active | .Paused => .paused | .Retired => .retired
def unstatus : RSL.EntryStatus → VerifierEntryStatusV1
 | .pending => .Pending | .active => .Active | .paused => .Paused | .retired => .Retired
@[simp] theorem status_back (x : VerifierEntryStatusV1) : unstatus (status x) = x := by cases x <;> rfl
@[simp] theorem status_forth (x : RSL.EntryStatus) : status (unstatus x) = x := by cases x <;> rfl
#print axioms status_back
#print axioms status_forth
end NND_Carrier
'''
(E/'NND_StatusCarrier.lean').write_text(status);prev='NND_StatusCarrier'
for n,typ,target in [('RegistryV1','VerifierRegistryV1','RegistryV1'),('RegistryV2','VerifierRegistryV2','RegistryV2'),('EntryV1','VerifierRegistryEntryV1','EntryV1'),('EntryV2','VerifierRegistryEntryV2','EntryV2')]:
 native='AdapterRw.aspis_statement.pool_v1.verifier_registry.'+typ
 pattern=r'^structure aspis_statement.pool_v1.verifier_registry.'+typ+r'\b(.*?)(?=\n/--)'
 body=re.search(pattern,src,re.M|re.S).group(1)
 fields=re.findall(r'^  (\w+) : ([^\n]+)',body,re.M)
 assert fields
 fn=n[0].lower()+n[1:];names=[]
 for f,t in fields:
  if 'Array Std.U8 32#usize' in t: conv='key'
  elif 'Std.U8' in t:conv='byte'
  elif 'Std.U64' in t:conv='slot'
  elif f=='status':conv='status'
  else:raise ValueError((f,t))
  names.append((f,conv))
 t='import '+prev+'\nset_option autoImplicit false\nnamespace NND_Carrier\n'
 t+='def '+fn+' (x : '+native+') : RSL.'+target+' :=\n { '+',\n   '.join(f+' := '+c+' x.'+f for f,c in names)+' }\n'
 t+='def un'+fn+' (x : RSL.'+target+') : '+native+' :=\n { '+',\n   '.join(f+' := un'+c+' x.'+f for f,c in names)+' }\n'
 for suf,arg,expr in [('back',native,'un'+fn+' ('+fn+' x)'),('forth','RSL.'+target,fn+' (un'+fn+' x)')]:
  t+='@[simp] theorem '+fn+'_'+suf+' (x : '+arg+') : '+expr+' = x := by\n cases x\n simp ['+fn+',un'+fn+']\n#print axioms '+fn+'_'+suf+'\n'
 t+='end NND_Carrier\n';module='NND_'+n+'Carrier';(E/(module+'.lean')).write_text(t);prev=module
