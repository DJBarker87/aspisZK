#!/usr/bin/env python3
"""Fail-closed V346 association inventory. Uses git objects, works in a sparse checkout."""
import argparse,collections,hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parent
BASE='85addf5a9764aa5e17d28bd6cf96bbda084447c5'
RECOUNT='47f44e887a502ad865ca0635745eae7cc4ac7b3b'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a])
def tree(rev):
 out={}
 for line in git('ls-tree','-r','-l',rev).decode().splitlines():
  meta,p=line.split('\t',1);m,t,h,n=meta.split()
  if t=='blob':out[p]={'git_blob':h,'bytes':int(n)}
 return out
T=tree(BASE)
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(h):
 proc.stdin.write((h+'\n').encode());proc.stdin.flush();hd=proc.stdout.readline().split()
 if len(hd)!=3:raise ValueError(hd)
 b=proc.stdout.read(int(hd[2]));assert proc.stdout.read(1)==b'\n';return b
def read(p):return blob(T[p]['git_blob'])
files={}
def pin(p):
 if p not in files:files[p]=dict(T[p],sha256=sha(read(p)))
 return p
def dump(name,obj):
 b=(json.dumps(obj,sort_keys=True,ensure_ascii=False,indent=1)+'\n').encode()
 if len(b)>18_000_000:
  items=list(obj.items()) if isinstance(obj,dict) else obj
  parts=[]
  for offset in range(0,len(items),1000):
   data=dict(items[offset:offset+1000]) if isinstance(obj,dict) else items[offset:offset+1000]
   part=name[:-5]+f'-part{offset//1000:03}.json';dump(part,data);bb=(D/part).read_bytes();parts.append({'path':part,'sha256':sha(bb),'bytes':len(bb)})
  b=(json.dumps({'sharded':parts,'kind':'dict' if isinstance(obj,dict) else 'list'},indent=1)+'\n').encode()
 assert len(b)<=20_000_000,(name,len(b));(D/name).write_bytes(b)
rs_pat=re.compile(r'(?:crates|programs|tools|docs|aeneas-verif)/[A-Za-z0-9_./+\-]+\.rs')
mod_pat=re.compile(r'\b(?:R1Z\.)?PV_[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*')
fn_pat=re.compile(r'\b(?:[A-Za-z_]\w*::)+[A-Za-z_]\w*')
lean=[p for p in T if p.endswith('.lean')]
bybase=collections.defaultdict(list)
for p in lean:bybase[Path(p).stem].append(p)
roots=[p for p in lean if Path(p).stem.startswith('PV_') or '/lean/R1Z/' in p]
queue=collections.deque(roots);modules={};unresolved=collections.defaultdict(list)
def candidates(m):
 suffix=m.replace('.','/')+'.lean';opts=[p for p in bybase.get(m.split('.')[-1],[]) if p==suffix or p.endswith('/'+suffix)]
 return opts or bybase.get(m.split('.')[-1],[])
while queue:
 p=queue.popleft()
 if p in modules:continue
 b=read(p);s=b.decode(errors='replace');pin(p)
 imports=[]
 for line in s.splitlines():
  z=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
  if not z:continue
  for name in re.findall(r'[A-Za-z_][\w.]*',z[1].split('--')[0]):
   opts=candidates(name);imports.append({'name':name,'candidates':opts,'resolution':'unique tracked path' if len(opts)==1 else 'ambiguous cohort; no variant adopted' if opts else 'external or missing; not replayed'})
   queue.extend(opts)
 paths=sorted(set(rs_pat.findall(s)))
 source=[]
 for rp in paths:
  source.append({'path':pin(rp) if rp in T else rp,'status':'textual source reference; association unverified','present_at_release':rp in T})
 generated=[]
 for ln,line in enumerate(s.splitlines(),1):
  if re.search(r'(Source:|source:|source function|Rust function|rust function)',line):generated.append({'line':ln,'text':line[:700]})
 classes=[]
 for pat,label in [('own[-_ ]1|structural','own-1 structural'),('singleton|own[-_ ]2','exhaustive over a singleton input domain, deployed-configuration harness'),('reclassification|b3p6-1','reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)'),('aeneas|charon|automatically generated','extraction'),('differential','native differential'),('kani','Kani')]:
  if re.search(pat,s,re.I):classes.append(label)
 modules[p]={'root':p in roots,'imports':imports,'rust_references':source,'source_function_mentions':sorted(set(fn_pat.findall(s)))[:300], 'generated_source_annotations':generated[:120], 'declarations':re.findall(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(:{]+)',s,re.M),'evidence_classes_mentioned':classes,'evidence_records':[],'binding_status':'UNVERIFIED: references/imports do not prove source association'}
print('modules',len(modules),flush=True)
# Index receipts/documents by explicit module/Lean-path mentions, never infer a binding from co-occurrence.
modbases=collections.defaultdict(list)
for p in modules:modbases[Path(p).stem].append(p)
evidence=[];hash_claims=[];historical=[]
metadata=[p for p,r in T.items() if p.startswith('evidence/pv-') and p.endswith(('.json','.md','.jsonl')) and r['bytes']<5_000_000 and not any(x in p for x in ['/sources/','/input/','/source/'])]
for p in metadata:
 b=read(p);s=b.decode(errors='replace'); names=set(re.findall(r'\b(?:R1Z\.)?(PV_[A-Za-z0-9_]+)',s))
 # R1Z filenames (non-PV) mentioned explicitly.
 names.update(re.findall(r'R1Z[/.]([A-Za-z_][A-Za-z0-9_]*)',s))
 matched=set()
 for n in names:matched.update(modbases.get(n,[]))
 if not matched and not re.search(r'kani|extraction|Charon|Aeneas',s,re.I):continue
 pin(p);idx=len(evidence);evidence.append({'path':p,'modules':sorted(matched),'association':'discovery only; no automatic credit'})
 for m in matched:modules[m]['evidence_records'].append(idx)
 if not p.endswith('.json'):continue
 try:j=json.loads(s)
 except ValueError:continue
 def walk(x,loc=''):
  if isinstance(x,list):
   for i,y in enumerate(x):walk(y,loc+'/'+str(i))
  elif isinstance(x,dict):
   # Only paired file+digest fields; body/token/output digests never treated as whole-file hashes.
   path=next((x[k] for k in ['path','source_path','source','rust_source','file'] if isinstance(x.get(k),str) and x[k] in T and x[k].endswith(('.rs','.lean','.toml','.lock'))),None)
   if path:
    expected=x.get('sha256') or x.get('source_sha256')
    h=x.get('git_blob') or x.get('blob')
    if isinstance(expected,str) and re.fullmatch('[a-f0-9]{64}',expected):
     pin(path);hash_claims.append({'evidence':idx,'pointer':loc,'path':path,'recorded_sha256':expected,'release_sha256':files[path]['sha256'],'status':'IDENTICAL' if expected==files[path]['sha256'] else 'STALE_OR_NON_FILE_HASH: review required'})
    elif isinstance(h,str) and re.fullmatch('[a-f0-9]{40}',h):
     pin(path);hash_claims.append({'evidence':idx,'pointer':loc,'path':path,'recorded_git_blob':h,'release_git_blob':T[path]['git_blob'],'status':'IDENTICAL' if h==T[path]['git_blob'] else 'STALE'})
   for k,y in x.items():
    if isinstance(y,(dict,list)):walk(y,loc+'/'+k)
 walk(j)
print('evidence',len(evidence),'hash claims',len(hash_claims),flush=True)
# Recount9 is NOT on BASE. Record all row witnesses and compare exact blobs, retaining classification.
rpath='evidence/privacy-recount-20261026/recount9/rows9.json'
rb=git('show',RECOUNT+':'+rpath);rj=json.loads(rb);recount=[]
for row in rj:
 witnesses=[]
 for key,value in row.items():
  if key.startswith('definition_witnesses') and isinstance(value,list):
   for w in value:
    p=w.get('path');h=w.get('blob');expected=w.get('sha256')
    if not p:continue
    if p in T:pin(p)
    status='MISSING' if p not in T else 'STALE' if (h and h!=T[p]['git_blob']) or (expected and expected!=files[p]['sha256']) else 'IDENTICAL' if h or expected else 'UNPINNED'
    z={'path':p,'recorded_blob':h,'recorded_sha256':expected,'release_blob':T.get(p,{}).get('git_blob'),'status':status,'declaration':w.get('declaration')}
    if z not in witnesses:witnesses.append(z)
 recount.append({'id':row['id'],'name':row.get('name'),'definition':row.get('definition'),'status':row.get('recount9_status',row.get('status')),'theorem':row.get('theorem'),'witnesses':witnesses,'scope':'supplemental historical row; no migration credit'})
# Reachability inventories: preserve limitations, names are discovery keys and never association proof.
inventory_paths=['evidence/pv-l3a-20261029/instances.json','evidence/pv-l3a-20261029/calls.json','evidence/pv-l3a-20261029/unresolved-indirect.json','evidence/pv-diag-20261029/source-triggers.json','evidence/pv-b3p6-20261028/resume9/body-inventory.json','evidence/pv-b3p6-20261028/resume11/mir-inventory-resume11.json','evidence/pv-b3p6-20261028/resume11/deployed-inventory-source.json']
inventories=[];functions={}
for p in inventory_paths:
 pin(p);j=json.loads(read(p));inventories.append({'path':p,'scope':'inherited conservative inventory; not a complete reached-function graph'})
 if p.endswith('instances.json'):
  for row in j:
   for n in row.get('names',[]):functions.setdefault(n,{'origins':[],'source_path':None})['origins'].append(p)
 elif p.endswith('body-inventory.json'):
  family={x['family']:x['source'] for x in j['files']}
  for row in j['bodies']:
   n=(row.get('source') or {}).get('name',row.get('key'));sp=family[row['family']]
   # Map recorded inventory copies onto the deployed source only when file-identical.
   for orig in ['crates/aspis-r1-cost-probe/src/'+Path(sp).name]:
    if orig in T and T[orig]['git_blob']==T[sp]['git_blob']:sp=orig
   if sp in T:pin(sp)
   functions.setdefault(sp+'::'+str(n),{'origins':[],'source_path':sp})['origins'].append(p)
 elif p.endswith('source-triggers.json'):
  for row in j:
   sp=row['path'];s=read(sp).decode(errors='replace') if sp in T else '';pin(sp) if sp in T else None
   for n in re.findall(r'\bfn\s+(\w+)',s):functions.setdefault(sp+'::'+n,{'origins':[],'source_path':sp})['origins'].append(p)
# No reference matching alone is sufficient to remove a gap; list candidate references separately.
for n,row in functions.items():
 leaf=n.split('::')[-1].split('<')[0]
 row['candidate_modules']=[p for p,m in modules.items() if row['source_path'] and any(x['path']==row['source_path'] for x in m['rust_references']) and any(x.split('::')[-1]==leaf for x in m['source_function_mentions'])]
 row['status']='NO_VERIFIED_BINDING_IN_THIS_MANIFEST'
# Freeze wire and protocol definitions as exact files; constants retained literally, not interpreted.
protocol=[]
for p in T:
 if p.startswith(('crates/aspis-r1-cost-probe/src/','crates/aspis-statement/src/','crates/aspis-core/src/r0/')) and (p.endswith(('wire.rs','params.rs','parameters.rs','config.rs')) or 'parameter' in Path(p).stem):
  pin(p);s=read(p).decode(errors='replace');protocol.append({'path':p,'constants':re.findall(r'(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+[^;]+;',s),'identity':'whole source blob; no inferred numeric equivalence'})
# EJR authority conflicts are explicit, never silently choose a cohort.
ejr='evidence/envj-rebuild-20261026/EJR_final-inventory.json';pin(ejr);ej=json.loads(read(ejr));cohorts=[]
for name,item in ej.get('selected',{}).items() if isinstance(ej.get('selected'),dict) else []:
 cohorts.append({'module':name,'record':item})
dump('COHORTS.json',{'authority':ejr,'selected':ej.get('selected'),'resolved':ej.get('resolved'),'policy':'Recorded authority only; no object replay or alternate variant adoption'});dump('MODULES.json',modules);dump('EVIDENCE.json',evidence);dump('HASH-CLAIMS.json',hash_claims);dump('RECOUNT9.json',recount);dump('GAPS.json',functions);dump('PROTOCOL.json',protocol);dump('FILES.json',files)
manifest={'schema':'aspis.proved-shipped.v1','release_revision':BASE,'branch':'codex/pv-mf-20261029','ledger':'V346','status':'OPEN','release_target':{'client':'devnet_spend','toolchain':'rustc 1.94.1 e408947bfd200af42db322daf0fadfe7e26d3bd1; x86_64-unknown-linux-gnu','features':['r1p-check','aspis-r1-cost-probe/ct-host-prover'],'profile':'release; Cargo per-package overrides retained in Cargo.toml','recipe':'PV_MF_native.py','build_inputs':'build-inputs.json','artifacts':'artifacts.json','locks':['Cargo.lock','tools/r1-cost-probe/Cargo.lock'],'wire_and_parameters':'PROTOCOL.json'},'counts':{'root_paths':len(roots),'module_paths_with_import_variants':len(modules),'evidence_records':len(evidence),'file_hash_claims':len(hash_claims),'stale_or_nonfile_hash_claims':sum(x['status']!='IDENTICAL' for x in hash_claims),'recount_rows':len(recount),'recount_stale_witnesses':sum(x['status']=='STALE' for r in recount for x in r['witnesses']),'inventory_function_keys':len(functions),'verified_native_bindings':0},'recount9':{'revision':RECOUNT,'path':rpath,'git_blob':git('rev-parse',RECOUNT+':'+rpath).decode().strip(),'sha256':sha(rb),'present_at_release':rpath in T,'policy':'Supplemental audit only; compare each witness. No historical certificate migration.'},'inventories':inventories,'limitations':['All PV_* tracked variants and all R1Z tracked paths included conservatively; paths are distinct records, not an adopted Lean cohort.','Import candidate lists enumerate ambiguity; no source variant is silently substituted. This is not V397 closure replay.','Function/path/docstring/receipt co-occurrence is discovery, not own-1/b3p6-1 credit. Missing statement-by-statement binding or generation chains remain gaps.','Inventory membership is not actual reachability; pv-diag explicitly lacks complete whole-image effect closure, b3p6 includes inactive/unlinked candidates, l3a omits inline instances.','V370 compiler preservation, D381/D386 boundary, rdea-1, K-1/K-2 quarantine and final V397/V398/V399 retained.','No proofs or Lean/Kani invocations; no claimed premise removal.'],'parts':{}}
for p in ['MODULES.json','EVIDENCE.json','HASH-CLAIMS.json','RECOUNT9.json','GAPS.json','PROTOCOL.json','FILES.json','build-inputs.json','elf-inputs.json','PV_MF_native.py','PV_MF_manifest.py','PV_MF_check.py','PV_MF_rehash.py','COHORTS.json']+[p.name for p in sorted(D.glob('*-part*.json'))]:
 manifest['parts'][p]={'sha256':sha((D/p).read_bytes()),'bytes':(D/p).stat().st_size}
dump('MANIFEST.json',manifest);print(json.dumps(manifest['counts'],indent=2))
