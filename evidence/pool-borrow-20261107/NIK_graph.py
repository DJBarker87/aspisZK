"""Add compiler call edges conservatively; generic dispatch stays explicit."""
from pathlib import Path
import json,re,collections
E=Path(__file__).resolve().parent;d=json.loads((E/'NIK_CENSUS.json').read_text())
byname=collections.defaultdict(list)
for f in d['functions']:
 if f['mir_headers']:byname[f['name']].append(f)
def callee(expr):
 depth=0;raw=''
 for i,c in enumerate(expr):
  if c=='(' and depth==0:break
  if c=='<':depth+=1
  if c=='>' and depth and (i==0 or expr[i-1]!='-'):depth-=1
  raw+=c
 return raw
def unparameterize(s):
 out='';depth=0
 for i,c in enumerate(s):
  if c=='<':depth+=1;continue
  if c=='>' and depth and (i==0 or s[i-1]!='-'):depth-=1;continue
  if not depth:out+=c
 return out.replace('::::','::').strip(':')
edges=[]
for c in d['mir_calls']:
 raw=callee(c['expression']);simple=unparameterize(raw);name=simple.split('::')[-1];cands=byname.get(name,[])
 qualified=[f for f in cands if Path(f['path']).stem in simple.split('::')[:-1]]
 if qualified:cands=qualified
 if raw.startswith('<') and ' as ' in raw:
  # Trait-bound bodies are not silently instantiated from a matching name.
  status='SYMBOLIC_TRAIT_OR_FN';target=None
 elif len(cands)==1:status='RESOLVED_SOURCE_NAME';target=cands[0]['function']
 elif cands:status='AMBIGUOUS';target=None
 elif raw.startswith(('move ','copy ','_')):status='INDIRECT';target=None
 else:status='EXTERNAL_OR_COMPILER';target=None
 edges.append(dict(mir_line=c['mir_line'],caller=c['caller'],callee=raw,status=status,target=target,candidates=[f['function'] for f in cands] if not target else [],source_candidates=[dict(line=a['line'],expression=a['expression']) for f in d['functions'] if f['function']==c['caller'] for a in f['calls'] if a['callee']==name]))
roots=[f['function'] for f in d['functions'] if f['name']=='process_instruction' and f['mir_headers']]
graph=dict(frozen_revision=d['frozen_revision'],mir_sha256=d['mir_sha256'],method='MIR call-target spelling plus frozen source AST; generic/indirect dispatch explicitly unresolved; no assertion of complete deployed monomorphization',roots=roots,root_association='SDK-generated entrypoint/deserializer to physical Pool prestate is an OPEN boundary; emitted functions include generic/non-root-reachable bodies',edges=edges,counts=dict(collections.Counter(e['status'] for e in edges)))
(E/'NIK_GRAPH.json').write_text(json.dumps(graph,indent=1)+'\n')
print('NIK Pool graph retained: '+str(len(edges))+' calls; unresolved generic/indirect edges remain explicit')
