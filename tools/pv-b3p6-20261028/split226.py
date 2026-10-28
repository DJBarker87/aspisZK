"""Partition exact emitted definitions; no body transformations or new models."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'lean/PV_B3P_BytesEmission226.lean'
s=p.read_text();ns='PV_B3P_226'
beg=s.index('def aspis_core.field.M31.ZERO');end=s.index('\nend '+ns,beg)
body=s[beg:end]
starts=list(re.finditer(r'^def (\S+)',body,re.M))
names=['PV_B3P_ByteField226','PV_B3P_ByteField226','PV_B3P_ByteField226','PV_B3P_ByteAt226','PV_B3P_ByteChunk226','PV_B3P_ByteEncode226','PV_B3P_ByteProjectLevel226','PV_B3P_ByteProject226','PV_B3P_BytesRoot226']
imports={'PV_B3P_ByteField226':['PV_B3P_BytesTypes226'],'PV_B3P_ByteAt226':['PV_B3P_ByteField226'],'PV_B3P_ByteChunk226':['PV_B3P_ByteAt226'],'PV_B3P_ByteEncode226':['PV_B3P_ByteChunk226'],'PV_B3P_ByteProjectLevel226':['PV_B3P_BytesTypes226'],'PV_B3P_ByteProject226':['PV_B3P_ByteProjectLevel226'],'PV_B3P_BytesRoot226':['PV_B3P_ByteEncode226','PV_B3P_ByteProject226']}
assert len(starts)==len(names)
parts={};records=[]
for i,m in enumerate(starts):
 segment=body[m.start():starts[i+1].start() if i+1<len(starts) else len(body)]
 segment=re.sub(r'/--.*?-/\s*','',segment,flags=re.S) # source-location documentation only; a dangling doc comment requires a declaration
 if i==0: segment='@[global_simps, irreducible, rust_const \"aspis_core::field::{aspis_core::field::M31}::ZERO\"]\n'+segment
 parts.setdefault(names[i],[]).append((m[1],segment));records.append({'declaration':ns+'.'+m[1],'module':names[i],'exact_body_sha256':hashlib.sha256(segment.encode()).hexdigest()})
for module,items in parts.items():
 header=''.join('import '+m+'\n' for m in imports[module])+f'open Aeneas Aeneas.Std Result ControlFlow Error\nset_option maxRecDepth 2048\nset_option maxHeartbeats 1000000\nnamespace {ns}\n'
 text=header+''.join(seg for _,seg in items)+'\nend '+ns+'\n'+''.join('#print axioms '+ns+'.'+name+'\n' for name,_ in items)
 (D/'lean'/f'{module}.lean').write_text(text)
(D/'split226.json').write_text(json.dumps({'original_port_sha256':hashlib.sha256(s.encode()).hexdigest(),'body_edits':False,'records':records,'candidate_only':True},indent=2)+'\n')
print(json.dumps({'modules':list(parts),'declarations':len(records),'body_edits':False}))
