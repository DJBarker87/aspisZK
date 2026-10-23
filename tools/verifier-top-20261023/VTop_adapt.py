#!/usr/bin/env python3
"""Parameterize external functions, preserving the emitted stage bodies."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2]; E=R/'evidence/verifier-top-20261023/generated-complete/VTop_Stages'; O=R/'docs/research/100bit-spend-path-20261013/lean'
raw=(E/'Funs.lean.txt').read_text(); ext=(E/'FunsExternal_Template.lean.txt').read_text()
blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',ext,re.M)
fields=[];mapping={}
for i,(name,typ) in enumerate(blocks):
 typ=typ.strip();field='op'+str(i);mapping[name]=field
 if typ.startswith(':'):typ=typ[1:].strip()
 else:
  depth=0
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:break
  typ='∀ '+typ[:j].rstrip()+', '+typ[j+1:].lstrip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
fields.append('  unwrap32 : core.result.Result (Array Std.U8 32#usize) core.array.TryFromSliceError → Result (Array Std.U8 32#usize)')
f=raw.replace('import VTop_Stages.Types','import VTop_Types').replace('import VTop_Stages.FunsExternal\n','')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
f=f.replace('namespace VTop_Stages\n','namespace VTop_Stages\n\nstructure Ops where\n'+'\n'.join(fields)+'\n\n',1)
pat=lambda n:r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])'
for n in sorted(mapping,key=len,reverse=True):f=re.sub(pat(n),'ops.'+mapping[n],f)
for n in ['verifier.candidate.tx1','verifier.candidate.tx2_common','verifier.candidate.tx2_authenticated']:
 f=re.sub(pat(n),'('+n+' ops)',f)
 f=f.replace('def ('+n+' ops)','def '+n+' (ops : Ops)')
f=f.replace('core.result.Result.unwrap core.fmt.DebugTryFromSliceError','ops.unwrap32')
for a,b in [('verifier.Error.','AdapterRw.aspis_r1_cost_probe.verifier.Error.'),('verifier.Phase.','AdapterRw.aspis_r1_cost_probe.verifier.Phase.'),('transport.Variant.','AspisR1Stage2.transport.Variant.')]:f=f.replace(a,b)
f+='\n#print axioms VTop_Stages.verifier.candidate.tx1\n#print axioms VTop_Stages.verifier.candidate.tx2_common\n#print axioms VTop_Stages.verifier.candidate.tx2_authenticated\n'
(O/'VTop_Model.lean').write_text(f)
(E.parent/'adaptation.json').write_text(json.dumps({'raw_funs_sha256':hashlib.sha256(raw.encode()).hexdigest(),'model_sha256':hashlib.sha256(f.encode()).hexdigest(),'operations':mapping,'qualification':'Only imports, resource settings and explicit external-operation parameterization changed. The pure std array unwrap call is also an explicit operation (avoids backend Formatter axiom); shared value layouts are separately recorded in VTop_Types; no cone instance is asserted.'},indent=2)+'\n')
