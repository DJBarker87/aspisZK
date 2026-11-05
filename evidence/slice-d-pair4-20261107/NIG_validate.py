from pathlib import Path
import ast,json,hashlib,lzma,re,copy
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-pair3-20261106'
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Replay exactly the predecessor gate against its retained evidence. No edits.
node=next(n for n in ast.parse((P/'NHX_validate.py').read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='gate')
oldroots=[r for g in J(P/'NHX_AUDIT_ROOTS.json')['groups']for r in g]
oldcatalog={x['module']:x['imports']for l in(P/'NHX_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(l)]}
ns=dict(roots=oldroots,catalog=oldcatalog)
exec(compile(ast.Module(body=[node],type_ignores=[]),'unchanged NHX gate','exec'),ns)
oldraw=[json.loads(l[11:])for l in(P/'NHX_L084/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
oldscan=[json.loads(l)for l in(P/'NHX_final_audit/NHX_LOADED_scan.jsonl').read_text().splitlines()]
assert ns['gate'](*[J(P/n)for n in['NHX_CLOSED.json','NHX_LEDGER_DELTA.json','NHX_AUDIT.json','NHX_TRUST.json']],oldraw,oldscan,J(P/'NHX_NATIVE_VALIDATION.json'))
receipts=[J(p)for p in sorted(E.glob('NIG_[KLE][0-9][0-9][0-9]/receipt.json'))]
assert len(receipts)==len((E/'NIG_ATTEMPTS.jsonl').read_text().splitlines())
counts={k:sum(r['kind']=='kani'if k=='K'else r['kind']=='extract'if k=='E'else r['kind']not in['kani','extract']for r in receipts)for k in['K','L','E']}
assert counts['K']<=120 and counts['L']<=80 and counts['E']<=1
for r in receipts:
 a=r['attempt'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 for k in ['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert k in r
 assert int(r['peak_rss_kib'])<8*1024*1024 and str(r['swaps'])=='0'
 index=J(E/a/'SOURCE_INDEX.json')if(E/a/'SOURCE_INDEX.json').exists()else None
 for n,h in r['source_hashes'].items():
  data=lzma.decompress((E/index[n]['payload']).read_bytes())if index else(E/a/'sources'/n).read_bytes()
  assert hashlib.sha256(data).hexdigest()==h,(a,n)
 if r['kind']=='kani':
  assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']and J(E/(a+'-lock-check.json'))['unchanged']
  assert not J(E/(a+'-source-check.json'))['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true'and'-Copt-level=3'in r['env']['RUSTFLAGS']
current={r['module']:r for r in receipts if r['kind']=='lean'and r['exit_status']==0}
for m in J(E/'NIG_QUALIFIED_MODULES.json')+['NIG_COMBINED_IMPORT']:
 p=E/(m+'.lean');assert current[m]['source_hashes']['NIG_generated/'+p.name]==sha(p),(m,'current source')
 s=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s)
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s)
 for n in re.findall(r'^theorem (\w+)\b',s,re.M):assert '#print axioms '+n in s
 for line in current[m]['print_axioms']:
  assert 'sorryAx'not in line
  if 'does not depend on any axioms'not in line:assert set(re.findall(r'\[([^]]*)\]',line)[-1].split(', '))<={'propext','Classical.choice','Quot.sound',''}
closed,delta,audit,trust,native=[J(E/n)for n in['NIG_CLOSED.json','NIG_LEDGER_DELTA.json','NIG_AUDIT.json','NIG_TRUST.json','NIG_NATIVE_VALIDATION.json']]
raw=[json.loads(l[11:])for l in(E/audit['raw_ax2']/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
scan=[json.loads(l)for l in(E/'NIG_final_audit/NIG_LOADED_scan.jsonl').read_text().splitlines()]
roots=[r for g in J(E/'NIG_AUDIT_ROOTS.json')['groups']for r in g]
catalog={x['module']:x['imports']for l in(E/'NIG_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(l)]}

def gate(c,d,a,t,nn,rr,ss):
 assert c['driver_root_status']==c['finish_relation_status']=='OPEN'
 assert c['new_composed_functions']==c['new_composed_rows']==1
 assert {r for f in c['functions']for r in f['rows']}=={'TX2:045'}
 assert d['new_closed_rows']==['TX2:045']and d['new_count']==1
 assert d['no_other_status_change']and d['not_a_premise_retirement']and d['validator_checks_added_only']and not d['base_change']
 assert a['status']=='PASS'and a['standard_only']and a['fixture']=='NIG_L028'
 assert a['dangling']==a['incompatible_owners']==a['import_mismatches']==0
 assert not t['added']and not t['removed']and not t['privacy_changed']and not t['two_transaction_design_changed']and'NOT ESTABLISHED'in t['headline']
 assert nn['status']=='PASS'and nn['qualified_rows']==['TX2:045']and len(nn['filled_windows'])==24 and nn['covered_prefix_cell_pairs']==2080
 assert nn['clone_pair']==['NIG_K094','NIG_K095']and nn['kmx_core_negative_controls']==['NIG_K092','NIG_K093']
 assert nn['no_native_field_products']and nn['no_writable_static']and nn['no_function_pointer']
 assert len(rr)==len(roots)and {r['root']for r in rr}==set(roots)
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in rr)
 assert len(ss)==a['modules']and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']and r['imports']==catalog[r['module']]for r in ss)
 for f in c['functions']:
  assert f['status']=='CLOSED'and f['domain']and not f['inner_hypotheses_remaining']
  assert f['lean_root']in roots and f['combined_replay']==a['combined']and f['ax2']==f['scan']==a['raw_ax2']
 return True
assert gate(closed,delta,audit,trust,native,raw,scan)
mutations=[('close pair',0,lambda x:x.update(driver_root_status='CLOSED')),('hide callee premise',0,lambda x:x['functions'][0]['inner_hypotheses_remaining'].append('reserve success')),('change old status',1,lambda x:x.update(no_other_status_change=False)),('remove trust',3,lambda x:x['removed'].append('Std')),('miss window',4,lambda x:x['filled_windows'].pop()),('miss position',4,lambda x:x.update(covered_prefix_cell_pairs=2079)),('missing clone control',4,lambda x:x.update(clone_pair=[])),('missing KMX control',4,lambda x:x.update(kmx_core_negative_controls=[])),('native product',4,lambda x:x.update(no_native_field_products=False)),('writable static',4,lambda x:x.update(no_writable_static=False)),('nonstandard axiom',5,lambda x:x[0]['walked_axioms'].append('sorryAx')),('missing root',5,lambda x:x.pop()),('missing module',6,lambda x:x.pop()),('dangling',6,lambda x:x[0]['dangling'].append({'bad':True})),('wrong import',6,lambda x:x[0]['imports'].append('NIG_Invalid'))]
results=[]
for label,i,mutate in mutations:
 args=copy.deepcopy([closed,delta,audit,trust,native,raw,scan]);mutate(args[i])
 try:gate(*args)
 except(AssertionError,KeyError):results.append(dict(mutation=label,rejected=True))
 else:raise AssertionError('accepted '+label)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
(E/'NIG_VALIDATOR_TESTS.json').write_text(json.dumps(dict(tests=results,all_rejected=True),indent=2)+'\n')
(E/'NIG_VALIDATION.json').write_text(json.dumps(dict(status='PASS',counts=counts,predecessor_gate='unchanged NHX gate via AST',predecessor_sha256=sha(P/'NHX_validate.py'),new_checks_only=True,new_rows=1,roots=len(raw),modules=len(scan),mutations_rejected=len(results)),indent=2)+'\n')
print('PASS additive validator; filled045 CLOSED; pair129/finish115 OPEN')
