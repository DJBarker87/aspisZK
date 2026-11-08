"""Offline final verification. Never launches Lean, the host, or another audit."""
import pathlib,json,lzma,hashlib,re,subprocess
E=pathlib.Path(__file__).parent;i=json.loads((E/'INVENTORY.json').read_text());blob=(E/'COLLECTED_EVIDENCE.json.xz').read_bytes();mf=json.loads((E/'COLLECTED_MANIFEST.json').read_text());assert hashlib.sha256(blob).hexdigest()==mf['archive_sha256'];raw=lzma.decompress(blob);assert hashlib.sha256(raw).hexdigest()==mf['uncompressed_sha256'];files=json.loads(raw)
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
for k,v in files.items():
 if k.startswith('evidence/admission-') and k.endswith('.json'):assert json.loads(v)['allowed'] is True,k
for r in receipts:
 if r.get('command'):
  cmd=r['command']
  if 'systemd-run' in cmd:
   for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in cmd,(r['attempt'],cap)
 if r.get('accepted') and 'swaps' in r:assert str(r['swaps'])=='0',r['attempt']
assert {r['attempt'] for r in receipts if not r.get('accepted')}=={56500,56516,56520,56535,56537,56539}
snapshots=[r for r in receipts if r['target']=='snapshots' and r.get('accepted')];assert len(snapshots)==1
comp=json.loads(files[f"evidence/STATEMENT_COMPARISONS-{snapshots[0]['attempt']}.json"]);assert len(comp)==47 and all(not r['differences'] and r['source']['exit']==0 and r['merged']['exit']==0 for r in comp)
expected=set(i['root_provenance']);groups=json.loads(lzma.decompress((E/'SNAPSHOT_PLAN.json.xz').read_bytes()));assert expected<={r for g in groups for r in g['roots']}
audits=[r for r in receipts if r['target']=='audit'];assert len(audits)==1 and audits[0]['accepted'] and audits[0]['exit']==0
a=audits[0]['attempt'];out=files[f'evidence/out-{a}.log'];results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in out.splitlines() if l.startswith('NEP62_RESULT ')];assert len(results)==len(expected) and {r['root'] for r in results}==expected
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
source=pathlib.Path('lean/PV_LIB_V1_RawAudit3.lean').read_text();base=pathlib.Path('lean/PV_LIB_SPEC_RawAuditSession19.lean').read_text()
def strip_arrays(s):
 if '-- V1_ARRAYS_BEGIN' in s:
  a=s.index('\n-- V1_ARRAYS_BEGIN');b=s.index('-- V1_ARRAYS_END',a)+len('-- V1_ARRAYS_END')
  s=s[:a]+s[b+1:]
 a=s.index('    (',s.index('let (modules, roots) :='));b=s.index('\n  let env ←',a)
 return s[:a]+s[b:]
assert strip_arrays(source)==strip_arrays(base)
changed=subprocess.check_output(['git','diff','--name-only',i['source_revision']],text=True).splitlines();repairs=json.loads((E/'IMPORT_CANONICALIZATION.json').read_text())['changes']
allowed={v['path'] for v in repairs.values()}|{'lean/PV_LIB_V1_StatementSnapshot.lean','lean/PV_LIB_V1_RawAudit2.lean','lean/PV_LIB_V1_RawAudit3.lean'}
assert all(p.startswith('evidence/pv-lib-20261107/') or p in allowed for p in changed)
for v in repairs.values():
 before=subprocess.check_output(['git','show',i['source_revision']+':'+v['path']],text=True);after=pathlib.Path(v['path']).read_text()
 strip=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))
 assert strip(before)==strip(after),v['path']
report=dict(source_revision=active['source_revision'],original_merge_revision=i['source_revision'],pv_modules=len(i['pv_modules']),freshly_compiled_pv=sum(m in compiled for m in i['pv_modules']),hash_reused_pv=sum(m in reuse for m in i['pv_modules']),root_count=len(results),source_type_groups=len(comp),type_differences=0,strict_audit=audits[0],strict_pass=True,unresolved=0,summary_mismatches=0,premises_removed=0,premises_added=0,owninit_witness_claim=False)
(E/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='strict_audit'},indent=2))
