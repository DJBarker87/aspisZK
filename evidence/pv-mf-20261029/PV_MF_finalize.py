#!/usr/bin/env python3
"""Add exact extraction associations, full inherited inventories, receipts and a fail-closed release gate."""
import collections,hashlib,json,lzma,re,subprocess
from pathlib import Path
import PV_MF_check as C
D=Path(__file__).resolve().parent;BASE='85addf5a9764aa5e17d28bd6cf96bbda084447c5'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a])
def dump(name,obj):
 b=(json.dumps(obj,sort_keys=True,indent=1)+'\n').encode()
 if len(b)>8_000_000:
  vals=list(obj.items()) if isinstance(obj,dict) else obj;parts=[]
  for k in range(0,len(vals),50):
   pn=f'{name[:-5]}-part{k//50:03}.json';v=dict(vals[k:k+50]) if isinstance(obj,dict) else vals[k:k+50];dump(pn,v);bb=(D/pn).read_bytes();parts.append({'path':pn,'sha256':sha(bb),'bytes':len(bb)})
  b=(json.dumps({'sharded':parts,'kind':'dict' if isinstance(obj,dict) else 'list'},indent=1)+'\n').encode()
 assert len(b)<20_000_000; (D/name).write_bytes(b)
M=C.load('MANIFEST.json');files=C.load('FILES.json');bindings=C.load('BINDINGS.json');refs=C.load('BINDING-MODULES.json');mods=C.load('MODULES.json')
tracked={}
for line in git('ls-tree','-r',BASE).decode().splitlines():
 meta,p=line.split('\t',1);tracked[p]=meta.split()[-1]
def read(p):return git('show',BASE+':'+p)
def pin(p):
 if p not in files:
  b=read(p);files[p]={'git_blob':tracked[p],'sha256':sha(b),'bytes':len(b)}
for rows in bindings.values():
 for r in rows:
  for f in r['release_source_candidates']:pin(f['path']);f['sha256']=files[f['path']]['sha256']
dump('BINDINGS.json',bindings)
# Exact import edges and source declaration associations are queryable via the module/blob indices.
association_by_rust=collections.defaultdict(set)
for p,h in refs.items():
 for r in bindings.get(h,[]):
  if r['rust_function']:association_by_rust[r['rust_function']].add(p)
functions=C.load('GAPS.json');inventories=M['inventories'];paths=['evidence/pv-l3a-20261029/function-index.json.xz']+[p for p in tracked if re.fullmatch(r'evidence/pv-diag-20261029/shard-\d\d.json.xz',p)]
excluded=[]
for p in paths:
 pin(p);j=json.loads(lzma.decompress(read(p)));inventories.append({'path':p,'scope':'linked function index' if isinstance(j,list) else 'compiled-corpus candidate inventory, not a reached-call proof'})
 if isinstance(j,list):
  for r in j:
   for n in r['names']:
    f=functions.setdefault(n,{'origins':[],'source_path':None});f['origins'].append(p)
 else:
  bad={r['path'] for r in j['inputs'] if r.get('actual_sha256')!=r.get('sha256')};excluded.extend(sorted(bad))
  for r in j['sites']:
   if r.get('file') in bad:continue
   for n in [r.get('function'),r.get('target_name')]:
    if not n:continue
    f=functions.setdefault(n,{'origins':[],'source_path':None});f['origins'].append(p)
for n,f in functions.items():
 f['origins']=sorted(set(f['origins']));f['exact_extraction_associations']=sorted(association_by_rust.get(n,[]));f['status']='RECORDED_EXTRACTION_ASSOCIATION_ORIGIN_UNVERIFIED' if f['exact_extraction_associations'] else 'NO_EXACT_DISCOVERED_FUNCTION_ASSOCIATION'
 f['reachability']='inventory candidate; actual privacy-path reachability must be established separately'
dump('GAPS.json',functions)
# Deduplicate concrete stale file pins; body/token digests remain a separate review list.
evidence=C.load('EVIDENCE.json');claims=C.load('HASH-CLAIMS.json');stale=[];seen=set();reviews=[];ecache={}
for r in claims:
 if r['status']=='IDENTICAL':continue
 p=evidence[r['evidence']]['path']
 if p not in ecache:
  try:ecache[p]=json.loads(read(p))
  except ValueError:ecache[p]={}
 obj=ecache[p]
 try:
  for k in r['pointer'].split('/')[1:]:obj=obj[int(k)] if isinstance(obj,list) else obj[k]
 except (KeyError,IndexError,TypeError):obj={}
 span_keys={'file_sha256','first_line','last_line','start','end','start_line','end_line','source_line','text','tokens'}
 is_span=bool(span_keys.intersection(obj)) or any(k in r['pointer'] for k in ['/application_bodies/','/raw_methods/','/bodies/'])
 is_file_pin='recorded_git_blob' in r or (not is_span and obj.get('sha256')==r.get('recorded_sha256'))
 if is_file_pin:
  key=(r['path'],r.get('recorded_sha256',r.get('recorded_git_blob')))
  if key not in seen:stale.append(dict(r,receipt_path=p,classification='STALE_FILE_ASSOCIATION_PIN; active-cohort relevance not inferred'));seen.add(key)
 else:reviews.append(r)
for row in C.load('RECOUNT9.json'):
 for w in row['witnesses']:
  if w['status']=='STALE':stale.append(dict(w,row=row['id'],classification='STALE_RECOUNT9_DEFINITION_WITNESS; historical row not migrated'))
dump('STALE.json',stale);dump('HASH-REVIEW.json',reviews)
protocol=[]
for row in C.load('build-inputs.json'):
 p=row['path']
 if not p.endswith('.rs'):continue
 text=read(p).decode(errors='replace');constants=re.findall(r'(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+[^;]+;',text)
 if constants or 'wire' in Path(p).stem or 'params' in Path(p).stem:
  pin(p);protocol.append({'path':p,'git_blob':files[p]['git_blob'],'sha256':files[p]['sha256'],'constants':constants,'identity':'whole shipped source blob; raw cfg alternatives retained; effective configuration is pinned by resolved-features.json and the rebuilt binary'})
dump('PROTOCOL.json',protocol);dump('FILES.json',files)
if (D/'SUPPLEMENT.json').exists():
 M['supplemental_historical_receipts']={'index':'SUPPLEMENT.json','count':len(C.load('SUPPLEMENT.json')),'credit':'discovery only; no historical certificate migration'}
M['inventories']=inventories;M['counts'].update(inventory_function_keys=len(functions),unique_extraction_blobs=len(bindings),extraction_declaration_associations=sum(map(len,bindings.values())),extraction_module_paths=len(refs),no_exact_discovered_function_association=sum(not f['exact_extraction_associations'] for f in functions.values()),stale_association_records=len(stale),hash_claims_requiring_body_vs_file_review=len(reviews))
M['release_target']['build_context']='BUILD-CONTEXT.json'
M['binding_map']={'structured_source_spans':'SOURCE-BINDINGS.json','modules':'MODULES.json','module_to_extraction_blob':'BINDING-MODULES.json','extraction_declarations':'BINDINGS.json','proof_source_import_policy':'Follow import candidate edges; ambiguous candidates remain ambiguous. Declaration associations describe recorded extraction names/locations, not a discharged generation/parity law.'}
M['counts']['identical_structured_source_span_associations']=sum(r['identity_status']=='IDENTICAL' for r in C.load('SOURCE-BINDINGS.json'))
M['excluded_inventory_inputs']=sorted(set(excluded));M['native_validation']={'scopes_used':3,'scopes_budget':30,'lean_used':0,'lean_budget':20,'kani_used':0,'receipt':'native02-receipt.json','fresh_artifact_rehash':'native03-receipt.json','failed_preflight':'native01-failure.json','features':'resolved-features.json','retained_binary':'/home/dombarker/project-offloads/codex-pv-mf-20261029/bin/devnet_spend','target_cache_removed':True}
M['release_gate']={'satisfied':['fresh client artifact hash equals pv-l3a','three retained release ELF hashes equal pins','551 inherited project input hashes plus root/tool manifests and locks identical'], 'unsatisfied':['candidate-adopted coherent module cohort and all generation hash chains','complete function-level structural/native/Kani associations at deployed features/profile','complete reached-function inventory and gap discharge','V397 final replay; V398 final axiom audit; V399 release binding'], 'premises_removed':[],'trust_changed':False}
# Pin every result/script/receipt component; checker validates shard hashes on load too.
M['parts']={}
for p in sorted(D.iterdir()):
 if p.is_file() and p.name not in ['MANIFEST.json','validation.json','release-gate-validation.json','REPORT.md'] and p.suffix in ['.json','.py','.txt','.log','.md']:
  b=p.read_bytes();M['parts'][p.name]={'sha256':sha(b),'bytes':len(b)}
dump('MANIFEST.json',M);print(json.dumps(M['counts'],indent=2))
