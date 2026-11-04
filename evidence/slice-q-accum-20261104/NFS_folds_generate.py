"""Reuse the CLOSED fold proofs with the SAME canonical field owners."""
from pathlib import Path
import json,functools,re,hashlib,sys
E=Path(__file__).resolve().parent;G=json.loads((E/'NFS_SOURCE_GRAPH.json').read_text());P=json.loads((E/'NFS_RETARGET_PROVENANCE.json').read_text());reuse=P['owner'];order=[];seen=set()
@functools.lru_cache(None)
def affected(n):return n in reuse or any(affected(d) for d in G.get(n,{}).get('imports',[]))
def visit(n):
 if n in seen or n in reuse or not affected(n):return
 seen.add(n)
 for d in G[n]['imports']:visit(d)
 order.append(n)
for n in ['NEI_CircleBridge','NEI_LineBridge']:visit(n)
rename={**P['namespace_map'],**{n:'NFS_'+n for n in order}}
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
imports=['Lean','NFN_PhaseTransport'];bodies=[];records=[]
for n in order:
 r=G[n];body=[]
 for line in r['source'].splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    mapped='NFS_Folds' if d in order else reuse.get(d,d)
    if mapped!='NFS_Folds' and mapped not in imports:imports.append(mapped)
  else:body.append(line)
 text=pat.sub(lambda m:rename[m.group()],'\n'.join(body)+'\n');bodies.append('-- BEGIN '+n+'\n'+text+'-- END '+n+'\n')
 records.append(dict(module=n,path=r['path'],original_sha256=hashlib.sha256(r['source'].encode()).hexdigest(),body_sha256=hashlib.sha256(text.encode()).hexdigest(),changes=['imports','proof namespace names']))
audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
for name,text in [('NFS_Folds.lean',''.join('import '+m+'\n' for m in imports)+'\n'+''.join(bodies)+audit),('NFS_FOLD_PROVENANCE.json',json.dumps(dict(order=order,files=records,namespace_map=rename),indent=1)+'\n')]:
 p=E/name
 if '--check' in sys.argv:assert p.read_text()==text
 else:p.write_text(text)
print('fold modules reused',len(order))
