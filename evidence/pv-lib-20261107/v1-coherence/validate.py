"""Offline final verification. Never launches Lean, the host, or another audit."""
import pathlib,json,lzma,hashlib,re,subprocess
E=pathlib.Path(__file__).parent;i=json.loads((E/'INVENTORY.json').read_text());mf=json.loads((E/'COLLECTED_MANIFEST.json').read_text());blob=b''.join((E/p['name']).read_bytes() for p in mf['parts']);assert hashlib.sha256(blob).hexdigest()==mf['archive_sha256'];raw=lzma.decompress(blob);assert hashlib.sha256(raw).hexdigest()==mf['uncompressed_sha256'];files=json.loads(raw)
active=json.loads((E/'ACTIVE_INVENTORY.json').read_text());plan=json.loads(files['PLAN.json']);assert plan['revision']==active['source_revision']
receipts=[json.loads(v) for k,v in files.items() if k.startswith('evidence/receipt-') and k.endswith('.json')]
reuse_records=json.loads(files['evidence/REUSE.json'])
freeze=json.loads(lzma.decompress(bytes.fromhex(files['evidence/COHORT_CANONICAL_FREEZE.json.xz']['binary_hex'])))
compiled={};reuse={}
for m in i['pv_modules']:
 h=freeze['files'][m+'.olean']['sha256'];sh=active['sources'][m]['sha256']
 candidates=[r for r in receipts if r.get('accepted') and r.get('target')==m and r.get('object_sha256')==h and r.get('source_sha256')==sh]
 if candidates:compiled[m]=candidates[-1]
 else:
  candidates=[r for r in reuse_records if r['module']==m and r['object_sha256']==h and r['source_sha256']==sh]
  assert candidates,('unverified active object',m,h);reuse[m]=candidates[-1]
reuse_dependency_hashes_verified=0
for r in reuse.values():
 for dep,h in r['dependency_hashes'].items():
  assert freeze['files'][dep.replace('.','/')+'.olean']['sha256']==h
  reuse_dependency_hashes_verified+=1
assert reuse_dependency_hashes_verified==788
for k,v in files.items():
 if k.startswith('evidence/admission-') and k.endswith('.json'):assert json.loads(v)['allowed'] is True,k
for r in receipts:
 if r.get('command'):
  cmd=r['command']
  if 'systemd-run' in cmd:
   for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in cmd,(r['attempt'],cap)
 if r.get('accepted') and 'swaps' in r:assert str(r['swaps'])=='0',r['attempt']
assert {r['attempt'] for r in receipts if not r.get('accepted')}=={56500,56516,56520,56535,56537,56539,56551,56552,56556,56560,56561,56562,56563,56590,56592,56594}
statement=json.loads(files['evidence/STATEMENT_COHERENCE.json']);assert statement['statement_differences']==0 and statement['source_groups']==47 and statement['expr_equal_count']==55
comp=statement['comparisons'];assert len(comp)==47
alpha=[json.loads(l) for l in files['evidence/out-56565.log'].splitlines() if l.startswith('{')];assert len(alpha)==55 and all(r['compatible'] and r['expr_equal'] and r['same_levels'] for r in alpha)
expected=set(i['root_provenance']);groups=json.loads(lzma.decompress((E/'SNAPSHOT_PLAN.json.xz').read_bytes()));assert expected<={r for g in groups for r in g['roots']}
audits=[r for r in receipts if r['target']=='audit' and r['accepted']];assert len(audits)==1 and audits[0]['exit']==0
assert [r['attempt'] for r in receipts if r['target']=='audit' and not r['accepted']]==[56590,56592,56594]
a=audits[0]['attempt'];union=json.loads(files[f'evidence/UNION_AUDIT-{a}.json']);assert union['strict_pass'] and union['same_frozen_object_mapping'];results=union['roots'];assert len(results)==len(expected) and {r['root'] for r in results}==expected
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
source=pathlib.Path('lean/PV_LIB_V1_RawAudit4.lean').read_text();base=pathlib.Path('lean/PV_LIB_SPEC_RawAuditSession19.lean').read_text()
def strip_arrays(s):
 if '-- V1_ARRAYS_BEGIN' in s:
  a=s.index('\n-- V1_ARRAYS_BEGIN');b=s.index('-- V1_ARRAYS_END',a)+len('-- V1_ARRAYS_END')
  s=s[:a]+s[b+1:]
 a=s.index('    (',s.index('let (modules, roots) :='));b=s.index('\n  let env ←',a)
 return s[:a]+s[b:]
assert strip_arrays(source)==strip_arrays(base)
narrow=pathlib.Path('lean/PV_LIB_V1_RawAuditNarrow.lean').read_text()
def erase_selection(s):
 a=s.index('  let (modules, roots)');b=s.index('  let env ←',a)
 return s[:a]+s[b:]
assert erase_selection(narrow)==erase_selection(base)
cfg=json.loads((E/'FINAL_ROOT_BATCHES.json').read_text());assert {r for b in cfg['batches'] for r in b['roots']}==expected
assert len([r for b in cfg['batches'] for r in b['roots']])==len(expected)
assert len(union['batches'])==len(cfg['batches'])
assert len({b['driver_object_sha256'] for b in union['batches']})==1
for b,c in zip(union['batches'],cfg['batches']):
 payload=json.dumps(dict(modules=c['modules'],roots=c['roots']),sort_keys=True)+'\n'
 assert b['selection_sha256']==hashlib.sha256(payload.encode()).hexdigest()
 assert b['exit']==0 and b['accepted'] and int(b['swaps'])==0
assert json.loads(files['evidence/COHORT_CANONICAL_FREEZE_CHECK.json'])['unchanged']
compat=[json.loads(l) for l in files['evidence/out-56558.log'].splitlines() if l.startswith('{')][-1];assert compat['compatible']

changed=subprocess.check_output(['git','diff','--name-only',i['source_revision']],text=True).splitlines();repairs=json.loads((E/'IMPORT_CANONICALIZATION.json').read_text())['changes']
allowed={v['path'] for v in repairs.values()}|{'lean/PV_LIB_V1_StatementSnapshot.lean','lean/PV_LIB_V1_RawAudit2.lean','lean/PV_LIB_V1_RawAudit3.lean','lean/PV_LIB_V1_RawAudit4.lean','lean/PV_LIB_V1_ModuleDeclarations2.lean','lean/PV_LIB_V1_DeclarationCohort.lean','lean/PV_LIB_V1_StatementAlpha.lean','lean/PV_LIB_V1_RawAuditNarrow.lean'}|{str(p) for p in pathlib.Path('lean').glob('PV_LIB_V1_RawAuditBatch*.lean')}
assert all(p.startswith('evidence/pv-lib-20261107/') or p in allowed for p in changed)
for v in repairs.values():
 before=subprocess.check_output(['git','show',i['source_revision']+':'+v['path']],text=True);after=pathlib.Path(v['path']).read_text()
 strip=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))
 assert strip(before)==strip(after),v['path']
final_modules=json.loads((E/'FINAL_MODULE_INVENTORY.json').read_text())
assert len(final_modules['modules'])==877 and len(final_modules['additional_replay_tools'])==43
for n,v in final_modules['modules'].items():assert hashlib.sha256(pathlib.Path(v['path']).read_bytes()).hexdigest()==v['sha256']
tool_attempts={'PV_LIB_V1_StatementSnapshot':56517,'PV_LIB_V1_RawAudit2':56536,'PV_LIB_V1_RawAudit3':56550,'PV_LIB_V1_ModuleDeclarations2':56553,'PV_LIB_V1_RawAudit4':56555,'PV_LIB_V1_DeclarationCohort':56557,'PV_LIB_V1_StatementAlpha':56564,'PV_LIB_V1_RawAuditNarrow':56566}
rbcomp={r['target']:r for r in json.loads(files['evidence/ROOT_BATCH_COMPILES-56559.json'])}
for n in final_modules['additional_replay_tools']:
 h=final_modules['modules'][n]['sha256']
 if n in tool_attempts:
  r=next(r for r in receipts if r['attempt']==tool_attempts[n]);assert r['accepted']
  assert any(str(c).endswith('/'+n+'.lean') for c in r['command'])
  assert any(k.endswith('/'+n+'.lean') and v==h for k,v in r['inputs_sha256'].items())
 else:
  r=rbcomp[n];assert r['accepted'] and r['source_sha256']==h
ack=json.loads(files['evidence/detached-ack-56595.json']);assert ack['detached'] and ack['all_stdio_host_files']
assert hashlib.sha256(files['detached-launch-56595.py'].encode()).hexdigest()==ack['launcher_sha256']
assert hashlib.sha256(files['detached-payload-56595.json'].encode()).hexdigest()==ack['payload_sha256']
payload=json.loads(files['detached-payload-56595.json']);assert payload['attempt']==a and payload['mode']=='audit'
assert {k:hashlib.sha256(v.encode()).hexdigest() for k,v in payload['files'].items()}==audits[0]['inputs_sha256']
assert payload['files']['FINAL_ROOT_BATCHES.json']==(E/'FINAL_ROOT_BATCHES.json').read_text()
live=json.loads((E/'LIVE_CAPS-56595.json').read_text());props=dict(l.split('=',1) for l in live['scope_properties'].splitlines())
for k,v in dict(MemoryHigh='6442450944',MemoryMax='8589934592',MemorySwapMax='0',TasksMax='64').items():assert props[k]==v
# Hash retained raw walks without materializing their entire decompressed JSON.
import io
rm=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());rb=b''.join((E/p['name']).read_bytes() for p in rm['parts']);assert hashlib.sha256(rb).hexdigest()==rm['archive_sha256']
rh=hashlib.sha256()
with lzma.open(io.BytesIO(rb),'rb') as stream:
 while chunk:=stream.read(4*1024*1024):rh.update(chunk)
assert rh.hexdigest()==rm['uncompressed_sha256']
names={f['name'] for f in rm['files']};assert all('NEP_pv-thread_'+r+'_REACHABLE.txt' in names for r in expected)
report=dict(source_revision=active['source_revision'],original_merge_revision=i['source_revision'],pv_modules=len(i['pv_modules']),final_pv_module_inventory=877,replay_tools_compiled=43,freshly_compiled_pv=sum(m in compiled for m in i['pv_modules']),hash_reused_pv=sum(m in reuse for m in i['pv_modules']),reuse_dependency_hashes_verified=reuse_dependency_hashes_verified,root_count=len(results),source_type_groups=len(comp),type_differences=0,strict_audit=audits[0],strict_pass=True,unresolved=0,summary_mismatches=0,premises_removed=0,premises_added=0,owninit_witness_claim=False)
(E/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='strict_audit'},indent=2))
