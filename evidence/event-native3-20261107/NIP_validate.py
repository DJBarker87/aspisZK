from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
def read(p):return json.loads((E/p).read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
scopes=[read(str(p.relative_to(E))) for p in sorted(E.glob('NIP_L*/receipt.json'))]
assert len(scopes)==14
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for x in scopes:
 a=x['attempt'];ad=read(a+'-admission.json')
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert x['exit_status']==0 and x['limits']==expected and int(x['swaps'])==0
 if x['kind']=='lean':assert '-M7000' in x['command']
 if x['kind']=='link':assert '-O3' in x['command']
 for name,h in x['source_hashes'].items():assert digest(E/a/'sources'/name)==h
 # Legacy runner key denotes this committed source-input manifest, not a cache census.
 assert x['deps_fingerprint']['cache_imports_manifest_sha256']==digest(E/'NIP_INPUT_PINS.json')
 assert x['deps_fingerprint']['selected_objects']
for p in E.glob('NIP_NEP_*.xz'):
 assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==p.with_suffix('.sha256').read_text().strip()
a=read('NIP_AUDIT.json');assert len(a['raw_roots'])==8 and len(a['fixtures'])==8
standard={'propext','Classical.choice','Quot.sound'}
for row in a['raw_roots']:assert row['equal'] and set(row['walked_axioms'])<=standard
for i,row in enumerate(a['fixtures']):
 assert row['equal']
 assert bool(row['walked_axioms'])==(i<4)
assert a['scan']['modules']==14794 and a['scan']['exit_status']==0
assert all(a['scan'][k]==0 for k in ['dangling','incompatible_owners','import_mismatches'])
assert not read('NIP_CLOSED.json')['closed_predicates']
assert not read('NIP_LEDGER_DELTA.json')['inventory_promotions']
for x in read('NIP_LEDGER_DELTA.json')['theorems']:assert x['status']=='OPEN' and not x['declared']
for p in E.glob('*.lean'):
 if p.name=='NIP_ProofDriver.lean':continue
 assert not re.search(r'^\s*(theorem|def|axiom|opaque|abbrev|structure|inductive)\s',p.read_text(),re.M)
 assert not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text())
census=read('NIP_SOURCE_CENSUS.json')
for p,identity in census['tree_identity'].items():
 now=subprocess.check_output(['git','rev-parse','HEAD:'+p],cwd=R,text=True).strip()
 assert now==identity['frozen']==identity['current']
for row in census['inputs']:
 raw=subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=R)
 assert hashlib.sha256(raw).hexdigest()==row['sha256']
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
assert read('NIP_EXPORT.json')['seed_verified']==107
print('NIP validation PASS: receipts, raw audits, fidelity fixtures, scan, frozen trees, and zero promotions')
