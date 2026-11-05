"""Strict additive NHI qualification. No predecessor predicate/status is relaxed."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,copy
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/n).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
rs=[];payloads={}
for p in sorted(E.glob('NHI_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());rs.append(r);a=r['attempt']
 for k in ['module','command','source_revision','source_tree_dirty','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits']:assert k in r,(a,k)
 assert r['limits']==limits and str(r['swaps'])=='0',(a,'resource gate')
 ad=J(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True,(a,'admission')
 assert 'timed out'not in(E/a/'stdout.log').read_text().lower(),a
 assert r['exit_status']not in[124,137],a
 if r['kind']=='lean'and r['exit_status']==0:assert all('sorryAx'not in s for s in r['print_axioms']),a
 if a.startswith('NHI_K'):
  g=J(a+'-graph-check.json');lock=J(a+'-lock-check.json');source=J(a+'-source-check.json')
  assert not source['errors']and g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true'and '-Copt-level=3'in r['env']['RUSTFLAGS']
  root=next(x for x in g['selected_closure']if x['name']=='aspis-r1-cost-probe')
  statement=next(x for x in g['selected_closure']if x['name']=='aspis-statement')
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(root['features'])
  assert {'r0','pool-v1-kernel'}<=set(statement['features'])
  assert '--locked'not in r['native_command']and '--no-default-features'not in r['native_command']
  assert r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s'
 index=J(a+'/SOURCE_INDEX.json');assert set(index)==set(r['source_hashes']),(a,'source archive coverage')
 for n,row in index.items():
  h=row['sha256'];path=E/row['payload']
  if h not in payloads:
   raw=lzma.decompress(path.read_bytes());assert len(raw)==row['bytes']and hashlib.sha256(raw).hexdigest()==h
   payloads[h]=row['payload']
  assert h==r['source_hashes'][n],(a,n)
counts={k:sum(r['attempt'].startswith('NHI_'+p)for r in rs)for k,p in [('kani','K'),('lean_audit','L'),('extraction','E')]}
assert counts=={'kani':120,'lean_audit':90,'extraction':3}
assert len(rs)==213 and len([json.loads(x)for x in(E/'NHI_ATTEMPTS.jsonl').read_text().splitlines()])==213
native=J('NHI_NATIVE_VALIDATION.json');assert native['pairs']==59 and not native['field_multiplication_native']and not native['quarantined']and not native['suspended']
assert len(J('NHI_SCALAR_REUSE.json')['rows'])==50
latest={}
for r in rs:
 if r['kind']=='lean'and r['exit_status']==0:latest[r['module']]=r
for p in E.glob('NHI_*.lean'):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',p.read_text()),p
 if 'Extracted'not in p.stem and 'FilledTypes'not in p.stem:assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
 assert p.stem in latest,('uncompiled owned module',p)
 r=latest[p.stem];assert sha(p)==r['source_hashes']['NHI_generated/'+p.name],p
 for name in re.findall(r'^theorem (\w+)\b',p.read_text(),re.M):assert '#print axioms '+name in p.read_text(),(p,name)
closed=J('NHI_CLOSED.json');delta=J('NHI_LEDGER_DELTA.json');audit=J('NHI_AUDIT.json');trust=J('NHI_TRUST.json');batch=J('NHI_final_audit/RESULT.json')
base=json.loads(lzma.decompress((E.parent/'ledger9-20261105/NGZ_LEDGER.json.xz').read_bytes()));baseline={r['row']:r for r in base['rows']};assert len(baseline)==599
for f in closed['functions']:
 assert f['status']=='CLOSED'and f['inner_hypotheses_remaining']==[]
 for row in f['rows']:assert baseline[row]['composed_status']=='OPEN'and baseline[row]['function']==f['function']
 for a in[f['combined_replay'],f['ax2'],f['scan']]:assert J(a+'/receipt.json')['exit_status']==0
raw=[json.loads(l[11:])for l in(E/'NHI_L092/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
roots=[r for g in J('NHI_AUDIT_ROOTS.json')['groups']for r in g]
scan=[json.loads(l)for l in(E/'NHI_final_audit/NHI_LOADED_scan.jsonl').read_text().splitlines()]
catalog={r['module']:r['imports']for l in(E/'NHI_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in[json.loads(l)]}
assert len(scan)==13606 and all(list(dict.fromkeys(r['loader_imports']))==r['imports']==catalog.get(r['module'])for r in scan)
assert J('NHI_L015/NHI_ProofDriver_BINARY_PIN.json')['sha256']==batch['proof_driver_sha256']==J('NHI_L092/NHI_ProofDriver_BINARY_PIN.json')['sha256']
fx=[json.loads(l[11:])for l in(E/'NHI_L015/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
assert len(fx)==8 and all(r['equal']and bool(r['walked_axioms'])==(i<4)for i,r in enumerate(fx))
assert sha(E/'NHI_NFA_WALKER.c.txt')==batch['walker_c_sha256']=='c041aabaccba69e3775f0e23a03c553968a05ec89f39e86bb830731ed1ec2420'

def gate(c,d,a,t,b,rr,ss):
 assert c['new_composed_rows']==c['new_composed_functions']==2 and c['driver_root_status']=='OPEN'
 assert {r for f in c['functions']for r in f['rows']}=={'TX2:130','TX2:131'}
 assert set(d['new_closed_rows'])=={'TX2:130','TX2:131'}and d['new_count']==2 and d['no_other_status_change']and d['not_a_premise_retirement']
 assert a['status']=='PASS'and a['combined']=='NHI_L091'and a['raw_ax2']==a['scan']=='NHI_L092'and a['roots']==103 and a['modules']==13606
 assert not t['added']and not t['removed']and not t['privacy_changed']and not t['two_transaction_design_changed']and 'NOT ESTABLISHED'in t['headline']
 assert b['status']=='PASS'and b['standard_only']and not b['dangling']and not b['incompatible_owners']and not b['import_mismatches']
 assert len(rr)==103 and {r['root']for r in rr}==set(roots)
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rr)
 assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in ss)
 return True
assert gate(closed,delta,audit,trust,batch,raw,scan)
tests=[]
for label,i,mutate in[
 ('inflated closure count',0,lambda x:x.update(new_composed_rows=3)),
 ('pair silently closed',0,lambda x:x.update(driver_root_status='CLOSED')),
 ('delta status predicate weakened',1,lambda x:x.update(no_other_status_change=False)),
 ('premise retirement claimed',1,lambda x:x.update(not_a_premise_retirement=False)),
 ('final raw audit missing',2,lambda x:x.update(raw_ax2='NHI_L087')),
 ('new trust hidden',3,lambda x:x['added'].append('bad')),
 ('trust removed',3,lambda x:x['removed'].append('P6')),
 ('headline falsely established',3,lambda x:x.update(headline='established')),
 ('dangling node',4,lambda x:x.update(dangling=1)),
 ('incompatible owner',4,lambda x:x.update(incompatible_owners=1)),
 ('import mismatch',4,lambda x:x.update(import_mismatches=1)),
 ('missing root',5,lambda x:x.pop()),
 ('nonstandard axiom',5,lambda x:x[0]['walked_axioms'].append('sorryAx')),
 ('raw/summary disagreement',5,lambda x:x[0].update(equal=False)),
 ('scanner defect ignored',6,lambda x:x[0].update(imports_match=False))]:
 values=[closed,delta,audit,trust,batch,raw,scan];values[i]=copy.deepcopy(values[i]);mutate(values[i])
 try:gate(*values)
 except AssertionError:tests.append(label)
 else:raise AssertionError('accepted mutation '+label)
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs']).returncode==0
assert not J('NHI_FROZEN_PINS.json')['elf_rebuild_trigger']
assert not J('NHI_CLEANUP.json')['cache_deleted']and not J('NHI_CLEANUP.json')['keys_handled']
export=J('NHI_EXPORT.json');assert export['admission']['exit']==0 and export['admission']['reservation']['allowed']is True
assert not list(E.rglob('__pycache__'))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,('oversize',str(p))
result=dict(status='PASS',counts=counts,new_composed_rows=2,new_rows=['TX2:130','TX2:131'],raw_roots=103,modules=13606,headline='NOT ESTABLISHED',new_trust=False,no_trust_removed=True,full_release_replay=False,shipped_source_unchanged=True,elf_rebuild_trigger=False,negative_validator_mutations_rejected=len(tests))
(E/'NHI_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');(E/'NHI_VALIDATOR_TESTS.json').write_text(json.dumps(dict(status='PASS',rejected=tests),indent=2)+'\n')
(E/'NHI_VALIDATOR_PROVENANCE.json').write_text(json.dumps(dict(baseline='../slice-d-finish3-20261106/NHE_validate.py',baseline_sha256=sha(E.parent/'slice-d-finish3-20261106/NHE_validate.py'),checks_removed=0,added=['NHI_validate.py','NHI_native_validate.py','NHI_validate_scalar.py'],source_snapshots='NHI_ALL_SHARED_INPUTS.json',global_ledger_unchanged=True),indent=2)+'\n')
print(json.dumps(result))
