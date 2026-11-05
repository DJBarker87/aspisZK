"""Read-only inherited gate plus strict NIQ support/open-edge validation."""
from pathlib import Path
import ast,copy,hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-pair4-20261107'
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Execute only predecessor's pure gate; all output artifacts belong to NIQ.
old=next(n for n in ast.parse((P/'NIG_validate.py').read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='gate')
ns=dict(roots=[r for g in J(P/'NIG_AUDIT_ROOTS.json')['groups']for r in g],catalog={x['module']:x['imports']for l in(P/'NIG_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(l)]})
exec(compile(ast.Module(body=[old],type_ignores=[]),'unchanged NIG pure gate','exec'),ns)
oldraw=[json.loads(l[11:])for l in(P/'NIG_L082/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
oldscan=[json.loads(l)for l in(P/'NIG_final_audit/NIG_LOADED_scan.jsonl').read_text().splitlines()]
assert ns['gate'](*[J(P/n)for n in['NIG_CLOSED.json','NIG_LEDGER_DELTA.json','NIG_AUDIT.json','NIG_TRUST.json','NIG_NATIVE_VALIDATION.json']],oldraw,oldscan)
receipts=[J(p)for p in sorted(E.glob('NIQ_[KL][0-9][0-9][0-9]/receipt.json'))]
assert len(receipts)==len((E/'NIQ_ATTEMPTS.jsonl').read_text().splitlines())==24
for r in receipts:
 a=r['attempt'];ad=J(E/(a+'-admission.json'))
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['peak_rss_kib'])<8*1024*1024 and int(r['swaps'])==0
 for k in ['command','module','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert k in r
 index=J(E/a/'SOURCE_INDEX.json')if(E/a/'SOURCE_INDEX.json').exists()else None
 for n,h in r['source_hashes'].items():
  data=lzma.decompress((E/index[n]['payload']).read_bytes())if index else(E/a/'sources'/n).read_bytes()
  assert hashlib.sha256(data).hexdigest()==h,(a,n)
 if r['kind']=='kani':
  assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']
  assert J(E/(a+'-lock-check.json'))['unchanged']
  assert not J(E/(a+'-source-check.json'))['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true'and'-Copt-level=3'in r['env']['RUSTFLAGS']
  root=next(x for x in J(E/(a+'-graph-check.json'))['selected_closure']if x['name']=='aspis-r1-cost-probe')
  assert set(root['features'])=={'default','private-leaf-salts','optimized-terminal','program-build'}
mods=['NIQ_RawWindows','NIQ_AllocationError','NIQ_FieldDomains','NIQ_ResultEncoding','NIQ_PairComposition','NIQ_FinishComposition','NIQ_COMBINED_IMPORT']
current={r['module']:r for r in receipts if r['kind']=='lean'and r['exit_status']==0}
for m in mods:
 s=(E/(m+'.lean')).read_text();assert current[m]['source_hashes']['NIQ_generated/'+m+'.lean']==sha(E/(m+'.lean'))
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s)
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s)
 for n in re.findall(r'^theorem (\w+)\b',s,re.M):assert '#print axioms '+n in s
 for line in current[m]['print_axioms']:
  assert 'sorryAx'not in line
  if 'does not depend on any axioms'not in line:assert set(re.findall(r'\[([^]]*)\]',line)[-1].split(', '))<={'propext','Classical.choice','Quot.sound',''}
closed,delta,audit,native=[J(E/n)for n in['NIQ_CLOSED.json','NIQ_LEDGER_DELTA.json','NIQ_AUDIT.json','NIQ_NATIVE_VALIDATION.json']]
raw=[json.loads(l[11:])for l in(E/'NIQ_final_audit/raw.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
scan=[json.loads(l)for l in(E/'NIQ_LOADED_scan.jsonl').read_text().splitlines()]
roots=[r for g in J(E/'NIQ_AUDIT_ROOTS.json')['groups']for r in g]
catalog={x['module']:x['imports']for l in(E/'NIQ_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(l)]}
fixtures=[json.loads(l[11:])for l in(E/'NIQ_L013/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
expected=[['NEP_Planted.'+n+'Ax']for n in['match','private','proof','aux']]+[[],[],[],[]]
assert [r['walked_axioms']for r in fixtures]==expected and all(r['equal']for r in fixtures)
assert J(E/'NIQ_L013/NIQ_ProofDriver_BINARY_PIN.json')==J(E/'NIQ_L014/NIQ_ProofDriver_BINARY_PIN.json')
assert J(E/'NIQ_L013/NIQ_Driver_BINARY_PIN.json')==J(E/'NIQ_L015/NIQ_Driver_BINARY_PIN.json')
for pair in native['pairs']:
 for k,exit in [('positive',0),('control',1)]:
  n=pair[k];assert J(E/n/'receipt.json')['exit_status']==exit
  s=(E/n/'stdout.log').read_text()
  assert 'VERIFICATION:- SUCCESSFUL'in s if exit==0 else'assertion failed: good'in s
assert 'assertion failed: target[0] != source[0]'in(E/'NIQ_K009/stdout.log').read_text()
assert sha(E.parent.parent/native['kmx_patch']['path'])==native['kmx_patch']['sha256']
assert not re.search(r'\bstatic\b|Option\s*<\s*fn', (E/'NIQ_gap_cuts.patch').read_text())
assert not subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs'],text=True).strip()
for r in J(E/'NIQ_INPUT_PINS.json')['files']:
 p=E.parent.parent/r['path'];assert sha(p)==r['sha256']

def gate(c,d,a,n,rr,ss):
 assert c['root']=='AspisR1.RPx_Deployed.deployed'and c['headline_status']=='NOT ESTABLISHED'
 assert c['new_composed_rows']==0 and c['new_closed_rows']==[] and c['model_support_is_not_native_closure']
 assert not c['new_trust_rows']and not c['pending_trust_used']
 assert {f['row']for f in c['functions']}=={'TX2:129','TX2:115'}
 assert all(f['status']=='OPEN'and f['complete_obligation']and f['remaining']and f['retained_root_domain']for f in c['functions'])
 assert d['new_closed_rows']==[]and d['new_count']==0 and d['no_other_status_change']and not d['base_change']and d['not_a_premise_retirement']
 assert not d['new_trust_rows']and not d['removed_trust_rows']
 assert a['standard_only']and a['scan_exit']==0 and a['raw_child_exit']==0 and a['not_a_native_composition_certificate']
 assert a['dangling']==a['incompatible_owners']==a['import_mismatches']==0
 assert len(n['pairs'])==3 and not n['quarantined']and not n['suspended']and n['new_composed_rows']==[]
 assert n['kmx_negative']=='NIQ_K009'
 assert len(rr)==len(roots)==22 and {r['root']for r in rr}==set(roots)
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rr)
 assert len(ss)==a['modules']==13743
 assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']and r['imports']==catalog[r['module']]for r in ss)
 return True
args=[closed,delta,audit,native,raw,scan];assert gate(*args)
mutations=[('promote pair',0,lambda x:x['functions'][0].update(status='CLOSED')),('promote finish',0,lambda x:x['functions'][1].update(status='CLOSED')),('hide remaining',0,lambda x:x['functions'][0].update(remaining='')),('hide caller domain',0,lambda x:x['functions'][1].update(retained_root_domain='')),('count support as closure',0,lambda x:x.update(new_composed_rows=1)),('use pending trust',0,lambda x:x['pending_trust_used'].append('NIN-R2')),('weaken model distinction',0,lambda x:x.update(model_support_is_not_native_closure=False)),('change base',1,lambda x:x.update(base_change=True)),('remove trust',1,lambda x:x['removed_trust_rows'].append('P6')),('false axiom pass',2,lambda x:x.update(standard_only=False)),('missing pair control',3,lambda x:x['pairs'].pop()),('missing KMX control',3,lambda x:x.update(kmx_negative='')),('quarantined credit',3,lambda x:x['quarantined'].append('K1')),('suspended credit',3,lambda x:x['suspended'].append('K1')),('nonstandard axiom',4,lambda x:x[0]['walked_axioms'].append('sorryAx')),('missing root',4,lambda x:x.pop()),('dangling',5,lambda x:x[0]['dangling'].append('bad')),('duplicate owner',5,lambda x:x[0]['duplicate_owners'].append('bad')),('wrong import',5,lambda x:x[0]['imports'].append('NIQ_BAD')),('missing module',5,lambda x:x.pop())]
results=[]
for label,i,f in mutations:
 xs=copy.deepcopy(args);f(xs[i])
 try:gate(*xs)
 except(AssertionError,KeyError):results.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('accepted '+label)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
(E/'NIQ_VALIDATOR_TESTS.json').write_text(json.dumps(dict(tests=results,all_rejected=True),indent=2)+'\n')
(E/'NIQ_VALIDATION.json').write_text(json.dumps(dict(status='PASS supporting evidence; rows OPEN',counts=J(E/'NIQ_FINAL_RESOURCES.json')['counts'],new_closed_rows=[],predecessor_gate='unchanged NIG pure gate via AST; read only',predecessor_source_sha256=sha(P/'NIG_validate.py'),roots=len(raw),modules=len(scan),mutations_rejected=len(results)),indent=2)+'\n')
print('PASS: 3 native gap pairs;22 standard roots;13743 clean modules;20 rejected mutations;0 new CLOSED rows')
