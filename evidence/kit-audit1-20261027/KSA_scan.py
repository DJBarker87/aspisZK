from pathlib import Path
import re,json,subprocess,hashlib,collections,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
# Importing this module refreshes only this job's deterministic lexical inventory.
import KSA_inventory as I
E=Path(__file__).resolve().parent
ix=json.loads((E/'KSA_merged_sources.json').read_text())
def qualified(p,line,name):
 stack=[]
 for s in I.clean(p.read_text()).splitlines()[:line-1]:
  m=re.match(r'^\s*namespace\s+(\S+)',s)
  if m:stack.append(m[1]);continue
  if re.match(r'^\s*(noncomputable\s+)?section\b',s):stack.append('');continue
  if re.match(r'^\s*end(?:\s|$)',s) and stack:stack.pop()
 prefix='.'.join(x for x in stack if x)
 return (prefix+'.' if prefix else '')+name
inventory=json.loads((E/'KSA_inventory.json').read_text())
for r in inventory['rows']:r['kernel_name']=qualified(Path(r['file']),r['line'],r['name'])
# Successor definitions are new mathematical adapters, never silently called emitted bodies.
for mod,path in ix.items():
 if not (mod.startswith('XRo_Join_') or mod.startswith('XSd_')):continue
 p=Path(path)
 for d in I.decls(p):
  if d['kind'] in ['theorem','lemma']:continue
  inventory['rows'].append(dict(file=str(p),file_sha256=I.sha(p),line=d['line'],name=d['name'],kernel_name=qualified(p,d['line'],d['name']),kind=d['kind'],counterpart='library model',raw_body_line=None,text_comparison='successor adapter, not raw emission',verdict='UNDETERMINED',reason='Adapter/model definition; does not supply universal emitted association.'))
(E/'KSA_inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
# Parse kernel edges, retaining proof and statement dependencies, including generated equations.
graph={};imports=set()
for attempt in ['KSA_L023','KSA_L024']:
 for line in (E/attempt/'stdout.log').read_text().splitlines():
  if line.startswith('KSA_IMPORT '):imports.add(line[len('KSA_IMPORT '):])
  if line.startswith('KSA_DEP '):
   r=json.loads(line[len('KSA_DEP '):]);graph.setdefault(r['name'],r)
# The same global spelling belongs to different nominal cohorts in separate sessions.
# Keep each environment independently, rather than merging colliding globals.
envs=[]
for attempt in ['KSA_L023','KSA_L024']:
 g={}
 for line in (E/attempt/'stdout.log').read_text().splitlines():
  if line.startswith('KSA_DEP '):
   r=json.loads(line[8:]);g[r['name']]=r
 envs.append((attempt,g))
source_theorems=[]
for mod,path in ix.items():
 p=Path(path)
 for d in I.decls(p):
  if d['kind'] in ['theorem','lemma']:source_theorems.append(dict(module=mod,file=path,line=d['line'],name=qualified(p,d['line'],d['name'])))
# Seed ALL explicit declarations in each hand-written model, not just the three known failures.
seed_modules={Path(r['file']).stem for r in inventory['rows'] if Path(r['file']).stem!='XRn_Join_Funs'}
# LP descendants duplicate these modules with names-only provenance; retain conservative status.
seed_modules|={n for n in ix if '_Kit_' in n or n in ['LPo_CircleModel','XRk_CircleModel','XRk_ByteFields']}
exact=[];covered=set()
for attempt,g in envs:
 seeds={n for n,r in g.items() if r['module'] in seed_modules and not r['theorem']}
 rev=collections.defaultdict(list)
 for n,r in g.items():
  for ref in r['refs']:rev[ref].append(n)
 witness={s:[s] for s in seeds};queue=collections.deque(seeds)
 while queue:
  n=queue.popleft()
  for parent in rev[n]:
   if parent not in witness:witness[parent]=[parent]+witness[n];queue.append(parent)
 for t in source_theorems:
  if t['name'] not in g or g[t['name']]['module']!=t['module']:continue
  covered.add((t['module'],t['name']))
  if t['name'] in witness:exact.append(dict(**t,environment=attempt,witness=witness[t['name']]))
# Static import closure candidates beyond the audited environments.
import_edges={n:re.findall(r'^import (\S+)',I.clean(Path(p).read_text()),re.M) for n,p in ix.items()}
def risk_path(mod,seen=None):
 if mod in seed_modules:return [mod]
 seen=set() if seen is None else seen
 if mod in seen:return None
 seen.add(mod)
 for dep in import_edges.get(mod,[]):
  found=risk_path(dep,seen)
  if found:return [mod]+found
 return None
candidates=[]
for t in source_theorems:
 if (t['module'],t['name']) in covered:continue
 w=risk_path(t['module'])
 if w:candidates.append(dict(**t,import_path=w,status='UNDETERMINED dependency: conservative import candidate, no kernel use asserted'))
(E/'KSA_dependencies.json').write_text(json.dumps(dict(kernel_environments=[dict(attempt=a,constants=len(g)) for a,g in envs],explicit_theorem_count=len(source_theorems),kernel_covered_theorems=len(covered),exact_affected=exact,unqueried_import_candidates=candidates,source_theorems=source_theorems,source_imports=import_edges),indent=2)+'\n')
lines=['# Affected theorem inventory','',f'{len(exact)} explicit source theorem declarations have kernel dependency paths to kit models in the audited environments. {len(candidates)} further declarations are conservative import candidates, not proved dependencies. Each full path is in KSA_dependencies.json. No source-to-emission credit is inferred from either set.','', '| Theorem | Source | First model on kernel path |','|---|---|---|']
for r in exact:lines.append(f"| `{r['name']}` | {r['file']}:{r['line']} | `{r['witness'][-1]}` |")
lines+=['','## Unqueried import candidates','','These are conservatively withheld pending per-constant inspection; an import alone is not proof of use.','','| Theorem | Source | Model module on import path |','|---|---|---|']
for r in candidates:lines.append(f"| `{r['name']}` | {r['file']}:{r['line']} | `{r['import_path'][-1]}` |")
(E/'KSA_DEPENDENCIES.md').write_text('\n'.join(lines)+'\n')
print('source theorems',len(source_theorems),'kernel covered',len(covered),'affected',len(exact),'unqueried risk',len(candidates),'inventory',len(inventory['rows']))
