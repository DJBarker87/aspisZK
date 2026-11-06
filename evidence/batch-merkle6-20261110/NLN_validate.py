"""Read-only integrity and budget checks for the NLN evidence packet."""
from pathlib import Path
import hashlib,json,re,lzma
E=Path(__file__).resolve().parent
attempts=[json.loads(s) for s in (E/'NLN_ATTEMPTS.jsonl').read_text().splitlines() if s.strip()]
assert len({a['attempt'] for a in attempts})==len(attempts)
assert sum(a['kind']=='kani' for a in attempts)<=10
assert sum(a['kind']!='kani' for a in attempts)<=80
assert sum(a['kind']=='audit' and a['module']=='NLN_final_binary_gates' for a in attempts)<=2
proof=json.loads((E/'NLN_PROOF_SET.json').read_text())
checked=0
for a in attempts:
 receipt=json.loads((E/a['full_receipt']).read_text())
 ad=json.loads((E/(a['attempt']+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 resource=ad['reservation']['NLN_resource_preflight']
 assert resource['free_bytes']>=40000000000 and resource['own_workspace_bytes']<30000000000
 assert resource['cargo_target'].endswith('/codex-cx-batch-merkle6-20261110/NLN_target')
 for source,wanted in receipt['source_hashes'].items():
  p=E/a['attempt']/'sources'/source
  if p.is_file():actual=hashlib.sha256(p.read_bytes()).hexdigest()
  elif Path(str(p)+'.xz').is_file():actual=hashlib.sha256(lzma.decompress(Path(str(p)+'.xz').read_bytes())).hexdigest()
  elif Path(str(p)+'.ref.json').is_file():
   ref=json.loads(Path(str(p)+'.ref.json').read_text());q=E/ref['owned_input']
   data=lzma.decompress(q.read_bytes()) if ref.get('compression')=='xz' else q.read_bytes()
   actual=hashlib.sha256(data).hexdigest()
  else:raise AssertionError('Missing source '+str(p))
  assert actual==wanted,(str(p),actual,wanted)
  checked+=1
for module in proof['modules']:
 p=E/(module+'.lean');text=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',text,re.M)
 matched=[]
 for a in attempts:
  if a['module']==module and a['exit_status']==0 and a['kind']=='lean':
   receipt=json.loads((E/a['full_receipt']).read_text())
   if receipt['source_hashes'][module+'.lean']==hashlib.sha256(p.read_bytes()).hexdigest():matched.append(receipt)
 assert len(matched)==1,(module,len(matched))
 for theorem in re.findall(r'^theorem (\S+)',text,re.M):assert '#print axioms '+theorem in text,(module,theorem)
clauses=json.loads((E/'NLN_CALLER_CLAUSES.json').read_text())['rows'];assert len(clauses)==6
for row in clauses:
 source=(E/(row['module']+'.lean')).read_text()
 for clause in row['clauses']:assert clause['verbatim'] in source,(row['row'],clause['name'])
 assert not any(term in source.split('theorem root',1)[1].split(' :\n',1)[0] for term in ['native :','child :','success :','Ops','Run'])
if (E/'NLN_AX2_RESULT.json').exists():
 ax=json.loads((E/'NLN_AX2_RESULT.json').read_text());assert ax['exit_status']==0 and ax['all_equal'] and ax['all_standard_axioms']
 std={'propext','Classical.choice','Quot.sound'}
 assert set(proof['roots'])<=set(r['root'] for r in ax['results'])
 for r in ax['results']:assert r['equal'] and set(r['walked_axioms'])<=std and set(r['collect_axioms'])<=std
 fx=[json.loads(l.removeprefix('NEP_RESULT ')) for l in (E/'NLN_AUDIT1_FIXTURES.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
 assert len(fx)==8 and all(r['equal'] for r in fx)
 assert all(bool(r['walked_axioms'])==(r['root'].startswith('NEP_Planted.')) for r in fx)
 scan=json.loads((E/'NLN_NFX_RESULT.json').read_text());assert scan['exit_status']==0 and scan['dangling']==scan['duplicate_owners']==scan['imports_mismatch']==0
 if (E/'NLN_EXPORT_MANIFEST.json').exists():
  pin=json.loads((E/'NLN_EXPORT_MANIFEST.json').read_text());assert pin['free_bytes']>=40000000000 and pin['own_workspace_bytes']<30000000000 and pin['deleted']==0
  raw=lzma.decompress((E/'NLN_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NLN_CLOSURE_PINS.json.sha256').read_text().strip()
  library=json.loads((E/'NLN_LIBRARY_CONTINUITY.json').read_text());assert library['all_library_hashes_unchanged'] and library['same_LEAN_PATH']
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20000000,str(p)
 if p.is_dir():assert p.name!='__pycache__',str(p)
print(json.dumps(dict(integrity='PASS',scopes=len(attempts),source_snapshots_checked=checked,proof_modules=len(proof['modules']),new_theorems=len(proof['roots']),kani=sum(a['kind']=='kani' for a in attempts),compiler=sum(a['kind']=='lean' for a in attempts),link=sum(a['kind']=='link' for a in attempts),audit_and_retention=sum(a['kind']=='audit' for a in attempts),extraction=0,security_target_established=False)))
