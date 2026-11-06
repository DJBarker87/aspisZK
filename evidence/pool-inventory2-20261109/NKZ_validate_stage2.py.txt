"""Fail-closed inventory validation; no solver or theorem credit."""
from pathlib import Path
import json,lzma,hashlib,subprocess,copy,collections,re,tomllib
E=Path(__file__).resolve().parent;R=E.parents[1];F='b936275465600469312d1f058cdc91ea2a11f3dc';sha=lambda b:hashlib.sha256(b).hexdigest()
def load(n):
 p=E/n
 return json.loads(p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read())
def put(n,d):(E/n).write_text(json.dumps(d,sort_keys=True,indent=1)+'\n')
inv=load('NKZ_INVENTORY.json');ast={d['function']:d for d in load('NKZ_SOURCE_AST.json')};roots=load('NKZ_ROOTS.json');sources={}
for p in {x['source_file'] for x in inv['rows']+inv['off_review_rows']}:sources[p]=subprocess.check_output(['git','show',F+':'+p],cwd=R)
def check(d):
 rows=d['rows'];off=d['off_review_rows'];assert d['security_target_established'] is False and d['proof_credit']==0
 assert len(rows)==d['counts']['rows'];assert [r['id'] for r in rows+off]==[f'POOL:{i:03}' for i in range(1,len(rows+off)+1)]
 keys={r['function'] for r in rows};assert len(keys)==len(rows);assert set(d['roots'])<=keys
 assert d['roots']==sorted(x['function'] for x in roots['roots'] if x['classification']=='ON')
 assert len(off)==sum(o['function'] in ast and o['function'] not in keys for o in json.loads((R/'evidence/pool-borrow3-20261107/NIZ_OPEN_SITES.json').read_text())['owners']) and all(x['scope']=='OFF_REVIEW_NOT_ON_CLOSURE' for x in off)
 for r in rows+off:
  a=ast[r['function']];b=sources[r['source_file']];assert sha(b[a['body_range'][0]:a['body_range'][1]])==r['frozen_body_sha256']
  assert r['inventory_status']=='INVENTORY_ONLY_NO_CREDIT';assert r['mir_headers'],r['function']
  if r in rows:assert set(r['callees'])<=keys
 seen=set(d['roots'])|{roots['entry']};G={r['function']:r['callees'] for r in rows};q=collections.deque(sorted(seen))
 while q:
  for t in G[q.popleft()]:
   if t not in seen:seen.add(t);q.append(t)
 assert seen==keys
 assert sum(r['genuinely_new'] for r in rows)==d['counts']['genuinely_new']
 assert sum(bool(r['basis_overlap']) for r in rows)==d['counts']['shared_body_occurrences']
check(inv)
controls=[]
for label,mutate in [('missing_root',lambda d:d['rows'].pop(next(i for i,r in enumerate(d['rows']) if r['function']==d['roots'][0]))),('body_hash',lambda d:d['rows'][0].update(frozen_body_sha256='0'*64)),('false_promotion',lambda d:d.update(proof_credit=1)),('dropped_OFF_owner',lambda d:d['off_review_rows'].pop())]:
 d=copy.deepcopy(inv);mutate(d)
 try:check(d)
 except (AssertionError,KeyError):controls.append(dict(control=label,result='REJECTED'))
 else:raise AssertionError('accepted corruption '+label)
inputs=load('NKZ_INPUTS.json')
for p in inputs['inputs']:
 b=(E/p['path']).read_bytes();assert sha(b)==p['sha256']
 if p['path'].endswith('.xz'):assert sha(lzma.decompress(b))==p['uncompressed_sha256']
assert all(x['matches'] for x in load('NKZ_DEPLOYED_BUILD.json')['compiler_input_checks'])
# Full 599 row basis is immutable; compare exact key and body, preserve every status.
ledger=json.loads(lzma.open(R/'evidence/ledger19-20261108/NKN_LEDGER.json.xz').read());old={r['row']:r for r in ledger['rows']};assert len(old)==599
for r in inv['rows']:
 for m in r['basis_overlap']:
  o=old[m['row']];assert (o['function'],o['frozen_body_sha256'],o['status'])==(r['function'],r['frozen_body_sha256'],m['status'])
ob=load('NKZ_OBLIGATIONS.json');assert len(ob['held_sites'])==3 and len(ob['exclusive_guard_owners'])==6 and len(ob['accessors'])>0
ids={r['id'] for r in inv['rows']+inv['off_review_rows']}
assert all(x['row'] in ids for x in ob['held_sites']+ob['exclusive_guard_owners'])
assert all(ob['producers'][k] for k in ['POOL.prefix_to_cpi','POOL.read_to_settlement','NIB-P1','NIB-P2','NIB-P3','NIB-P4'])
tr=load('NKZ_TRACTABILITY.json');new=[x for x in tr['rows'] if x['genuinely_new'] is True];assert len(new)==inv['counts']['genuinely_new']
assert all(x['class_'] in ['A','B','C','D'] for x in new)
assert all(x['predecessor_failure'] and x['predecessor_failure']['attempt'] for x in tr['rows'] if x['class_']=='D')
# Every emitted source header is either resolved, kept as alternatives or classified generated/opaque.
g=load('NKZ_GRAPH.json');unmatched=[]
for h in g['unmatched_headers']:
 hdr=h['header']
 if h['conservative_owners']:kind='CONSERVATIVE_SOURCE_ALTERNATIVES_RETAINED'
 elif '<impl at ' in hdr:kind='DERIVED_OR_MACRO_IMPL: std/derive under (au); custom macro review retained'
 elif re.match(r'fn (entrypoint|__rust_|custom_panic)',hdr):kind='SDK_ENTRY_ALLOCATOR_PANIC_BOUNDARY'
 else:kind='GENERATED_CONSTRUCTOR_OR_UNRESOLVED_HEADER: retained for review, no credit'
 unmatched.append(dict(**h,disposition=kind))
put('NKZ_HEADER_REVIEW.json',dict(headers=unmatched,warning='Retained codegen/custom-macro records are not assumed proved; scope is source-function inventory, with derives/constructors/std interpreted at retained tool/library boundary.'))
# Every crate potentially reached: project compiler inputs, actual compiler externs/mono
# and a frozen-lock conservative dependency closure (target-specific branches retained).
lock=tomllib.loads(subprocess.check_output(['git','show',F+':Cargo.lock'],cwd=R).decode());packages=lock['package'];byname=collections.defaultdict(list)
for p in packages:byname[p['name']].append(p)
seen=set();q=collections.deque([('aspis-pool',None)])
while q:
 name,version=q.popleft()
 for p in byname[name]:
  if version and p['version']!=version:continue
  key=(p['name'],p['version'],p.get('source','workspace'))
  if key in seen:continue
  seen.add(key)
  for dep in p.get('dependencies',[]):
   words=dep.split();q.append((words[0],words[1] if len(words)>1 and words[1][0].isdigit() else None))
external_packages=[dict(name=p['name'],version=p['version'],source=p.get('source','workspace'),checksum=p.get('checksum'),scope='FROZEN_LOCK_CONSERVATIVE_TARGET_SUPERSET') for p in packages if (p['name'],p['version'],p.get('source','workspace')) in seen]
externs=[]
for crate in ['aspis_pool','aspis_core','aspis_statement']:
 cmd=load('NKZ_'+crate+'.command.json');externs.append(dict(crate=crate,extern_arguments=[cmd[i+1] for i,x in enumerate(cmd) if x=='--extern'],source_function_rows=sum(r['source_file'].startswith({'aspis_pool':'programs/aspis-pool/','aspis_core':'crates/aspis-core/','aspis_statement':'crates/aspis-statement/'}[crate]) for r in inv['rows'])))
put('NKZ_CRATES.json',dict(project_compilers=externs,dependency_closure=external_packages,target_superset_not_actual_calls=True,std_toolchain='rustc1.89.0-sbpf-solana-v1.52 plus exact retained compiler flags and P7; core/alloc are not Cargo.lock packages.',cross_program='Verifier/token/system are runtime CPI boundaries, not Rust library edges into verifier rows. Their behavior is not silently included in source-call closure.'))
# Inventory never edits anything outside own prefix directory.
changed=subprocess.check_output(['git','diff','--name-only',F,'--','crates','programs'],cwd=R,text=True).splitlines();assert not changed,changed
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
result=dict(status='PASS',controls=controls,counts=inv['counts'],frozen_revision=F,basis_sha256=sha((R/'evidence/ledger19-20261108/NKN_LEDGER.json.xz').read_bytes()),source_scripts={p.name:sha(p.read_bytes()) for p in E.glob('NKZ_*.py')},shipped_source_diff=[],formal_scopes=dict(Kani=0,Lean=0,MIR=0,extraction=0),proof_credit=0,target_established=False)
put('NKZ_VALIDATION.json',result)
print('NKS validation PASS: frozen body/graph/root/status checks; four corruption controls rejected; no shipped changes.')
