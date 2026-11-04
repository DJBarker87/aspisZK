"""Deterministic remaining-closure retarget; NFN objects are reused, never recopied."""
from pathlib import Path
import json,re,functools,hashlib,sys
E=Path(__file__).resolve().parent
G=json.loads((E/'NFS_SOURCE_GRAPH.json').read_text()); N=json.loads((E.parent/'slice-q-phase-20261104/NFN_RETARGET_PROVENANCE.json').read_text())
reuse=dict(N['module_owner']);reuse.update({'FIo_ReduceBounds':'RPt_FIo_ReduceBounds','JFv_RawExtractedSemanticCallOpsV20':'RPu_JFv_RawExtractedSemanticCallOpsV20'})
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
# Emit modules independently: smallest target first, no new generated bodies/options.
owner={n:'NFS_'+n.replace('.','_') for n in order};owner.update(reuse)
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
 emit(E/(owner[n]+'.lean'),''.join('import '+d+'\n' for d in imports)+'\n'+text+audit)
 records.append(dict(original_module=n,original_path=r['path'],original_sha256=hashlib.sha256(r['source'].encode()).hexdigest(),target_module=owner[n],body_sha256=hashlib.sha256(text.encode()).hexdigest(),changes=['imports','proof namespace names']))
emit(E/'NFS_RETARGET_PROVENANCE.json',json.dumps(dict(order=order,reuse=reuse,owner=owner,namespace_map=rename,files=records),indent=1)+'\n')
print('remaining modules',len(order));print('\n'.join(order))
