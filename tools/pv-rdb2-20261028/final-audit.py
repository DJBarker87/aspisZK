from pathlib import Path
import subprocess,json,hashlib,lzma,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2-20261028';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-rdb2-20261028'
rows=['V229','V230','V231','V238','V239','V240','V247','V256','V257','V258','V259']
for row in rows:
 j=json.loads((E/(row+'.json')).read_text());assert j['disposition']=='SUSPENDED' and not j['finding']
 b=lzma.decompress((E/(row+'-source-gate.json.xz')).read_bytes());assert hashlib.sha256(b).hexdigest()==(E/(row+'-source-gate.sha256')).read_text().strip()
 native=json.loads((E/j['deployed_native_receipt']).read_text());assert native['exit']==0 and native['swap']=='0' and native['resolved_features'] and 'release' in native['profile']
for n in ['rows','arithmetic','sha','ct','multilinear','leaves','sum','sampler','weights']:
 p=E/('native-'+n);meta=lzma.decompress((p/'metadata.json.xz').read_bytes());assert hashlib.sha256(meta).hexdigest()==(p/'metadata.json.sha256').read_text().strip()
 m=json.loads(meta);assert any(x['name']=='zeroize' and x['version']=='1.9.0' for x in m['packages'])
assert not subprocess.check_output(['git','diff','--name-only','6273e62061','--','crates','programs'],text=True).strip()
for p in R.glob('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDB2_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s)
 assert not re.search(r'^import .*XR',s,re.M)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
# Fingerprint the successful new proof objects before removing owned rebuildable caches.
code='''from pathlib import Path
import hashlib,json
D=Path(DIR);out={}
for m in ['R1Z/PV_RDB2_Layout','R1Z/PV_RDB2_Audit']:
 s=D/'lean-sources'/(m+'.lean');o=D/'lean-objects'/(m+'.olean')
 out[m]=dict(source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest())
print(json.dumps(out))
'''.replace('DIR',repr(D))
pins=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+shlex.quote(code)]))
for n,m in [(41101,'R1Z/PV_RDB2_Layout'),(41197,'R1Z/PV_RDB2_Audit')]:
 p=E/f'lean-{n}/receipt.json';j=json.loads(p.read_text());assert j['exit']==0 and j['source_sha256']==pins[m]['source_sha256']
 assert j['print_axioms'] and all('sorryAx' not in x for x in j['print_axioms']);j['accepted_axioms']=True
 j['profile']='N/A Lean value model; no native compilation';j['object_sha256']=pins[m]['object_sha256']
 if n==41197:
  j['dependency_fingerprint']={'R1Z.PV_RDB2_Layout':pins['R1Z/PV_RDB2_Layout']};j['deps_fingerprint']=hashlib.sha256(json.dumps(j['dependency_fingerprint'],sort_keys=True).encode()).hexdigest()
 p.write_text(json.dumps(j,indent=2)+'\n')
receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());receipts.append(dict(path=str(p.relative_to(E)),exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],axioms=j['print_axioms']))
(E/'combined-audit.json').write_text(json.dumps(dict(status='SUSPENDED HANDOFF; NO RESTORED CREDIT',rows=rows,restored=[],suspended=rows,findings=[],native_scopes=11,lean_attempts=[41100,41101,41197],kani=0,remaining_budget=dict(lean=97,native=109),proof_objects=pins,receipts=receipts,focused_replay=dict(new_layout_audit=41197,restored_row_replay=[],reason='No restored row exists; no historical source-law cone claimed replayed'),premises_removed=0,premises_added=0,premises_changed=0,passed_integrity_checks=True),indent=2)+'\n')
print('PASS integrity/disposition audit; eleven suspensions, zero restored')
