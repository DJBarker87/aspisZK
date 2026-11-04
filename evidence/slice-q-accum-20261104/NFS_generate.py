"""Deterministic remaining-closure retarget; NFN objects are reused, never recopied."""
from pathlib import Path
import json,re,functools,hashlib,sys
E=Path(__file__).resolve().parent
G=json.loads((E/'NFS_SOURCE_GRAPH.json').read_text()); N=json.loads((E.parent/'slice-q-phase-20261104/NFN_RETARGET_PROVENANCE.json').read_text())
reuse=dict(N['module_owner']);reuse['S1M31EmbeddingTotalV1']='RPz7_S1M31EmbeddingTotalV1';reuse.update({'FIo_ReduceBounds':'RPt_FIo_ReduceBounds','JFv_RawExtractedSemanticCallOpsV20':'RPu_JFv_RawExtractedSemanticCallOpsV20'})
@functools.lru_cache(None)
def affected(n):return n in reuse or any(affected(d) for d in G.get(n,{}).get('imports',[]))
order=[];seen=set()
def visit(n):
 if n in seen or not affected(n):return
 seen.add(n)
 if n in reuse:return
 for d in G[n]['imports']:visit(d)
 order.append(n)
visit('NEV_AccumPacket')
rename=dict(N['proof_namespace_map'])
rename.update({n:'NFS_'+n for n in order if '.' not in n})
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
# Batch dependent replay after the newly exposed canonical embedding cut.
groups=[];current=[];lines=0
for n in order:
 size=len(G[n]['source'].splitlines())
 if current and lines+size>850:groups.append(current);current=[];lines=0
 current.append(n);lines+=size
if current:groups.append(current)
owner={n:f'NFS_AccumPart{i:02}' for i,ns in enumerate(groups) for n in ns};owner.update(reuse)
batches={owner[n]:dict(imports=['Lean','NFN_PhaseTransport'],bodies=[]) for n in order}
records=[]
def emit(p,t):
 if '--check' in sys.argv:assert p.read_text()==t,str(p)
 else:p.write_text(t)
for n in order:
 r=G[n];imports=['Lean','NFN_PhaseTransport'];body=[]
 for line in r['source'].splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    d=owner.get(d,d)
    if d not in imports:imports.append(d)
  else:body.append(line)
 text='\n'.join(body)+'\n'; text=pat.sub(lambda m:rename[m.group()],text)
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 batch=batches[owner[n]]
 for d in imports:
  if d!=owner[n] and d not in batch['imports']:batch['imports'].append(d)
 batch['bodies'].append('-- BEGIN copied '+n+'\n'+text+'-- END copied '+n+'\n')
 records.append(dict(original_module=n,original_path=r['path'],original_sha256=hashlib.sha256(r['source'].encode()).hexdigest(),target_module=owner[n],body_sha256=hashlib.sha256(text.encode()).hexdigest(),changes=['imports','proof namespace names']))
for m,b in batches.items():emit(E/(m+'.lean'),''.join('import '+d+'\n' for d in b['imports'])+'\n'+''.join(b['bodies'])+audit)
emit(E/'NFS_RETARGET_PROVENANCE.json',json.dumps(dict(order=order,groups=groups,reuse=reuse,owner=owner,namespace_map=rename,files=records),indent=1)+'\n')
print('remaining modules',len(order));print('\n'.join(order))
