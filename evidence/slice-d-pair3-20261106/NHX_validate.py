"""Additive qualification. The predecessor gate is executed without edits."""
from pathlib import Path
import ast,copy,hashlib,json,lzma,re
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-pair2-20261106'
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
node=next(n for n in ast.parse((P/'NHM_validate.py').read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='gate')
oldroots=[r for g in J(P/'NHM_AUDIT_ROOTS.json')['groups']for r in g]
oldcatalog={r['module']:r['imports']for l in(P/'NHM_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in[json.loads(l)]}
ns=dict(roots=oldroots,catalog=oldcatalog)
exec(compile(ast.Module(body=[node],type_ignores=[]),'unchanged NHM gate','exec'),ns)
oldraw=[json.loads(l[11:])for l in(P/'NHM_L080/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
oldscan=[json.loads(l)for l in(P/'NHM_final_audit/NHM_LOADED_scan.jsonl').read_text().splitlines()]
assert ns['gate'](*[J(P/n)for n in['NHM_CLOSED.json','NHM_LEDGER_DELTA.json','NHM_AUDIT.json','NHM_final_audit/RESULT.json','NHM_TRUST.json']],oldraw,oldscan)
rs=[J(p)for p in sorted(E.glob('NHX_[KLE][0-9][0-9][0-9]/receipt.json'))]
assert len(rs)==len((E/'NHX_ATTEMPTS.jsonl').read_text().splitlines())
counts={k:sum(r['kind']=='kani'if k=='K'else r['kind']=='extract'if k=='E'else r['kind']not in['kani','extract']for r in rs)for k in['K','L','E']}
assert counts['K']<=120 and counts['L']<=80 and counts['E']<=2
for r in rs:
 a=r['attempt'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 for n in['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert n in r
 assert int(r['peak_rss_kib'])<8*1024*1024 and str(r['swaps'])=='0'
 index=J(E/a/'SOURCE_INDEX.json')if(E/a/'SOURCE_INDEX.json').exists()else None
 for name,h in r['source_hashes'].items():
  raw=lzma.decompress((E/index[name]['payload']).read_bytes())if index else(E/a/'sources'/name).read_bytes()
  assert hashlib.sha256(raw).hexdigest()==h,(a,name)
 if r['kind']=='kani':
  assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']
  assert J(E/(a+'-lock-check.json'))['unchanged']
  assert not J(E/(a+'-source-check.json'))['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true'and'-Copt-level=3'in r['env']['RUSTFLAGS']
current={r['module']:r for r in rs if r['kind']=='lean'and r['exit_status']==0}
for p in E.glob('NHX_*.lean'):
 assert p.stem in current,('current source uncompiled',p)
 assert current[p.stem]['source_hashes']['NHX_generated/'+p.name]==sha(p),p
 text=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',text),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',text),p
 for name in re.findall(r'^theorem (\w+)\b',text,re.M):assert '#print axioms '+name in text,(p,name)
 for line in current[p.stem]['print_axioms']:
  assert 'sorryAx'not in line
  if 'does not depend on any axioms' not in line:
   assert set(re.findall(r'\[([^]]*)\]',line)[-1].split(', '))<={'propext','Classical.choice','Quot.sound',''}
closed=J(E/'NHX_CLOSED.json');delta=J(E/'NHX_LEDGER_DELTA.json');audit=J(E/'NHX_AUDIT.json');trust=J(E/'NHX_TRUST.json')
raw=[json.loads(l[11:])for l in(E/audit['raw_ax2']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
scan=[json.loads(l)for l in(E/'NHX_final_audit/NHX_LOADED_scan.jsonl').read_text().splitlines()]
roots=[r for g in J(E/'NHX_AUDIT_ROOTS.json')['groups']for r in g]
catalog={r['module']:r['imports']for l in(E/'NHX_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in[json.loads(l)]}
native=J(E/'NHX_NATIVE_VALIDATION.json')
def gate(c,d,a,t,rr,ss,nn):
 assert c['driver_root_status']==c['finish_relation_status']=='OPEN'
 wanted={'TX2:133','TX2:135','TX2:139','TX2:140','TX2:143','TX2:144'}
 assert c['new_composed_rows']==c['new_composed_functions']==len(wanted)
 assert {r for f in c['functions']for r in f['rows']}==wanted
 assert d['new_closed_rows']==sorted(wanted)and d['new_count']==len(wanted)
 assert d['no_other_status_change']and d['not_a_premise_retirement']and d['validator_checks_added_only']
 assert a['status']=='PASS'and a['standard_only']and a['fixture']=='NHX_L017'
 assert a['dangling']==a['incompatible_owners']==a['import_mismatches']==0
 assert not t['added']and not t['removed']and not t['privacy_changed']and not t['two_transaction_design_changed']and'NOT ESTABLISHED'in t['headline']
 assert len(rr)==len(roots)and {r['root']for r in rr}==set(roots)
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rr)
 assert len(ss)==a['modules']and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']and r['imports']==catalog[r['module']]for r in ss)
 assert nn['status']=='PASS'and nn['arbitrary_message_qualified']and nn['kmx_negative_controls']==['NHX_K032','NHX_K033']
 assert nn['no_writable_static']and nn['no_function_pointer']and nn['source_erasure_validated']
 assert len(nn['pairs'])>=45
 assert set(nn['qualified_rows'])==wanted
 assert 'K112 positive with timed-out K113 control'in nn['excluded']
 assert c['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 for f in c['functions']:
  assert f['status']=='CLOSED'and not f['inner_hypotheses_remaining']and f['domain']
  assert f['combined_replay']==a['combined']and f['ax2']==f['scan']==a['raw_ax2']
  assert f['lean_root']in roots
 return True
assert gate(closed,delta,audit,trust,raw,scan,native)
mutations=[('close pair',0,lambda x:x.update(driver_root_status='CLOSED')),('close filled',0,lambda x:x['functions'][0]['rows'].append('TX2:045')),('hide callee premise',0,lambda x:x['functions'][0]['inner_hypotheses_remaining'].append('successful child')),('change old status',1,lambda x:x.update(no_other_status_change=False)),('claim retirement',1,lambda x:x.update(not_a_premise_retirement=False)),('silent trust',3,lambda x:x['added'].append('bad')),('nonstandard axiom',4,lambda x:x[0]['walked_axioms'].append('sorryAx')),('missing root',4,lambda x:x.pop()),('missing module',5,lambda x:x.pop()),('dangling reference',5,lambda x:x[0]['dangling'].append({'bad':True})),('wrong import',5,lambda x:x[0]['imports'].append('NHX_Invalid')),('zero-message promotion',6,lambda x:x.update(arbitrary_message_qualified=False)),('missing KMX control',6,lambda x:x.update(kmx_negative_controls=[])),('writable static',6,lambda x:x.update(no_writable_static=False)),('unvalidated erasure',6,lambda x:x.update(source_erasure_validated=False))]
results=[]
for label,i,mutate in mutations:
 args=copy.deepcopy([closed,delta,audit,trust,raw,scan,native]);mutate(args[i])
 try:gate(*args)
 except(AssertionError,KeyError):results.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('accepted '+label)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
(E/'NHX_VALIDATOR_TESTS.json').write_text(json.dumps(dict(tests=results,all_rejected=True),indent=2)+'\n')
(E/'NHX_VALIDATION.json').write_text(json.dumps(dict(status='PASS',counts=counts,predecessor_gate='unchanged NHM gate via AST',predecessor_sha256=sha(P/'NHM_validate.py'),new_checks_only=True,new_rows=len(closed['functions']),roots=len(raw),modules=len(scan),mutations_rejected=len(results)),indent=2)+'\n')
print('PASS additive validator; pair and finish OPEN')
