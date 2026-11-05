"""Strict additive qualification; predecessor gate is invoked byte-for-byte."""
from pathlib import Path
import ast,copy,hashlib,json,lzma,re
E=Path(__file__).resolve().parent;B=E.parent/'slice-d-pair-20261106'
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Reuse the exact predecessor acceptance predicate without executing its writers.
tree=ast.parse((B/'NHI_validate.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='gate')
ns={'roots':[r for g in J(B/'NHI_AUDIT_ROOTS.json')['groups']for r in g]}
exec(compile(ast.Module(body=[node],type_ignores=[]),'unchanged NHI gate','exec'),ns)
base_raw=[json.loads(l[11:])for l in(B/'NHI_L092/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
base_scan=[json.loads(l)for l in(B/'NHI_final_audit/NHI_LOADED_scan.jsonl').read_text().splitlines()]
assert ns['gate'](*[J(B/n)for n in ['NHI_CLOSED.json','NHI_LEDGER_DELTA.json','NHI_AUDIT.json','NHI_TRUST.json','NHI_final_audit/RESULT.json']],base_raw,base_scan)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
rs=[J(p)for p in sorted(E.glob('NHM_[KLE][0-9][0-9][0-9]/receipt.json'))]
assert len(rs)==202 and {p:sum(r['attempt'].startswith('NHM_'+p)for r in rs)for p in ['K','L','E']}=={'K':120,'L':80,'E':2}
assert len((E/'NHM_ATTEMPTS.jsonl').read_text().splitlines())==202
for r in rs:
 a=r['attempt'];assert r['limits']==limits and str(r['swaps'])=='0'
 assert int(r['peak_rss_kib'])<8*1024*1024
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 for k in ['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert k in r
 assert re.fullmatch('[0-9a-f]{40}',r['source_revision'])
 if r['kind']=='lean'and r['exit_status']==0:assert all('sorryAx'not in x for x in r['print_axioms'])
 assert r['exit_status']not in [124,137]
 index=J(E/a/'SOURCE_INDEX.json')if(E/a/'SOURCE_INDEX.json').exists()else None
 for n,h in r['source_hashes'].items():
  if index:
   row=index[n];raw=lzma.decompress((E/row['payload']).read_bytes());assert row['sha256']==h and len(raw)==row['bytes']
  else:raw=(E/a/'sources'/n).read_bytes()
  assert hashlib.sha256(raw).hexdigest()==h,(a,n)
latest={r['module']:r for r in rs if r['kind']=='lean'and r['exit_status']==0}
for p in E.glob('NHM_*.lean'):
 assert p.stem in latest,('uncompiled current module',p)
 assert latest[p.stem]['source_hashes']['NHM_generated/'+p.name]==sha(p),p
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',p.read_text()),p
 if p.stem not in ['NHM_WindowTypes','NHM_WindowExtracted','NHM_ControlTypes','NHM_ControlExtracted']:
  assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
 for n in re.findall(r'^theorem (\w+)\b',p.read_text(),re.M):assert '#print axioms '+n in p.read_text(),(p,n)
closed=J(E/'NHM_CLOSED.json');delta=J(E/'NHM_LEDGER_DELTA.json');audit=J(E/'NHM_AUDIT.json');batch=J(E/'NHM_final_audit/RESULT.json');trust=J(E/'NHM_TRUST.json')
raw=[json.loads(l[11:])for l in(E/'NHM_L080/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
scan=[json.loads(l)for l in(E/'NHM_final_audit/NHM_LOADED_scan.jsonl').read_text().splitlines()]
roots=[r for g in J(E/'NHM_AUDIT_ROOTS.json')['groups']for r in g]
catalog={r['module']:r['imports']for l in(E/'NHM_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in[json.loads(l)]}
def gate(c,d,a,b,t,rr,ss):
 assert c['new_composed_rows']==c['new_composed_functions']==4
 assert c['driver_root_status']==c['finish_relation_status']=='OPEN'
 wanted={'TX2:136','TX2:137','TX2:141','TX2:142'}
 assert {r for f in c['functions']for r in f['rows']}==wanted
 assert set(d['new_closed_rows'])==wanted and d['new_count']==4 and d['no_other_status_change']and d['not_a_premise_retirement']
 for f in c['functions']:
  assert f['status']=='CLOSED'and not f['inner_hypotheses_remaining']and f['domain']
  assert f['combined_replay']=='NHM_L078'and f['ax2']==f['scan']=='NHM_L080'
 assert a['status']==b['status']=='PASS'and a['standard_only']and b['standard_only']
 assert a['combined']=='NHM_L078'and a['statements']=='NHM_L079'and a['raw_ax2']==a['scan']=='NHM_L080'
 assert not t['added']and not t['removed']and not t['privacy_changed']and not t['two_transaction_design_changed']and'NOT ESTABLISHED'in t['headline']
 assert len(rr)==len(roots)==b['roots']and {r['root']for r in rr}==set(roots)
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rr)
 assert len(ss)==b['modules']and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']and r['imports']==catalog[r['module']]for r in ss)
 assert not b['dangling']and not b['incompatible_owners']and not b['import_mismatches']
 return True
assert gate(closed,delta,audit,batch,trust,raw,scan)
mutations=[('inflate count',0,lambda x:x.update(new_composed_rows=5)),('close pair',0,lambda x:x.update(driver_root_status='CLOSED')),('close filled',0,lambda x:x['functions'][0]['rows'].append('TX2:045')),('hide callee premise',0,lambda x:x['functions'][0]['inner_hypotheses_remaining'].append('successful child')),('change old status',1,lambda x:x.update(no_other_status_change=False)),('claim retirement',1,lambda x:x.update(not_a_premise_retirement=False)),('missing final scan',2,lambda x:x.update(scan='NHM_L059')),('nonstandard raw axiom',5,lambda x:x[0]['walked_axioms'].append('sorryAx')),('missing root',5,lambda x:x.pop()),('missing module',6,lambda x:x.pop()),('dangling ref',6,lambda x:x[0]['dangling'].append({'bad':True})),('wrong import',6,lambda x:x[0]['imports'].append('NHM_InvalidImportMutation')),('add trust silently',4,lambda x:x['added'].append('bad')),('claim headline',4,lambda x:x.update(headline='established'))]
results=[]
for label,i,mutate in mutations:
 args=copy.deepcopy([closed,delta,audit,batch,trust,raw,scan]);mutate(args[i])
 try:gate(*args)
 except(AssertionError,KeyError):results.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('accepted mutation '+label)
assert J(E/'NHM_NATIVE_VALIDATION.json')['pending']==[]
assert len(J(E/'NHM_NATIVE_VALIDATION.json')['pairs'])==46
assert len(J(E/'NHM_NATIVE_VALIDATION.json')['additional_corruption_controls'])==4
assert J(E/'NHM_L055/NHM_ProofDriver_BINARY_PIN.json')['sha256']==batch['proof_driver_sha256']
assert J(E/'NHM_WALKER_PIN.json')['byte_identical']and sha(E/'NHM_NFA_WALKER.c.txt')==batch['walker_c_sha256']
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
(E/'NHM_VALIDATOR_TESTS.json').write_text(json.dumps(dict(tests=results,count=len(results),all_rejected=True),indent=2)+'\n')
(E/'NHM_VALIDATION.json').write_text(json.dumps(dict(status='PASS',predecessor_gate='unchanged NHI gate, read-only AST extraction; no predicate relaxed',predecessor_validator_sha256=sha(B/'NHI_validate.py'),new_checks_only=True,attempts=len(rs),new_rows=4,raw_roots=len(roots),modules=len(scan),mutations_rejected=len(results)),indent=2)+'\n')
print('PASS additive validation; four helper rows only; pair/finish OPEN')
