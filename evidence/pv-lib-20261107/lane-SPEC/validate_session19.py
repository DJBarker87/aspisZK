"""Offline source/receipt/provenance checks. No Lean or raw replay."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
S=json.loads((L/'SESSION19_STATUS.json').read_text())
P=json.loads((L/'SESSION19_PROVENANCE.json').read_text())
standard={'propext','Classical.choice','Quot.sound'}
for v in P:
 a=v['attempt'];r=json.loads((L/f'receipt-{a}.json').read_text())
 assert r['accepted']==(a in S['accepted_focused'])
 if r['accepted']:
  path='lean/'+r['target']+'.lean';raw=(R/path).read_bytes()
  assert sha(raw)==r['source_sha256']
  assert sha(subprocess.check_output(['git','show',v['passing_source_commit']+':'+path],cwd=R))==r['source_sha256']
  assert int(r['exit'])==0 and int(r['swaps'])==0
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',raw.decode(),re.M)
  for line in r['axioms_summary_based']:
   assert 'sorryAx' not in line
   if 'depends on axioms:' in line:
    ax=line.split('depends on axioms:',1)[1].strip().strip('[]')
    assert set(x.strip() for x in ax.split(','))<=standard
 elif r['class']=='elaboration':
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
roots=json.loads((L/'SESSION19_RAW_ROOTS.json').read_text())
assert roots['count']==len(roots['roots'])==55
assert sha((R/'lean/PV_LIB_SPEC_RawAuditSession19.lean').read_bytes())==roots['driver_sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession17.lean').read_text()
new=(R/'lean/PV_LIB_SPEC_RawAuditSession19.lean').read_text()
assert old[old.index('\n  let env ←'):]==new[new.index('\n  let env ←'):]
assert not S['full_task_complete'] and not S['universal_contracts_inhabited']
for path in subprocess.check_output(['git','diff','--name-only','b2663b3dfc2'],cwd=R,text=True).splitlines():
 assert path.startswith('evidence/pv-lib-20261107/lane-SPEC/') or (path.startswith('lean/PV_LIB_SPEC_') and path.endswith('19.lean')),path
if S['strict_audit_passed']:
 A=json.loads((L/'SESSION19_RAW_AUDIT.json').read_text())
 assert A['exit']==0 and A['roots']==55 and A['all_equal'] and A['unresolved']==0 and A['standard_axioms_only']
 archive=lzma.decompress((L/'SESSION19_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
 assert sha(archive)==(L/'SESSION19_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
 graphs=json.loads(archive);M=json.loads((L/'SESSION19_RAW_GRAPH_MANIFEST.json').read_text())
 assert len(graphs)==len(M['files'])==55
 for f in M['files']:assert sha(graphs[f['name']].encode())==f['sha256']
print(json.dumps({'offline_checks':'PASS','logical_roots':55,'strict_audit_passed':S['strict_audit_passed'],'full_target_established':False}))
