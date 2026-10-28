from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb1-20261028';P=R/'docs/research/v8-r0-zk-20261009/lean'
expected=set('V164 V170 V178 V181 V182 V183 V184 V186 V187 V195 V198 V219'.split())
rows=[json.loads(p.read_text()) for p in (E/'rows').glob('*.json')];assert {x['row'] for x in rows}==expected
restored=sorted(x['row'] for x in rows if x['status']=='RESTORED');findings=sorted(x['row'] for x in rows if x['status']=='FINDING')
assert findings==['V178','V181'] and len(restored)==10
lean=[json.loads(p.read_text()) for p in sorted(E.glob('*-receipt.json'))];native=[json.loads(p.read_text()) for p in sorted(E.glob('*/receipt.json'))]
assert len(lean)<=100 and len(native)<=120
assert len({x['id'] for x in lean})==len(lean) and all(54700<=x['id']<=54799 for x in lean)
assert all(int(x['swap'])==0 for x in lean+native)
allowed={'propext','Classical.choice','Quot.sound'};axioms=set()
for receipt in lean:
 if receipt['exit']!=0:continue
 for line in receipt['print_axioms']:
  m=re.search(r'axioms: \[([^]]*)\]',line)
  if m:
   xs={x.strip() for x in m[1].split(',') if x.strip()};assert xs<=allowed;axioms.update(xs)
# Every final own module has a successful compile at exactly its current source hash.
modules=[]
for p in (P/'R1Z').glob('PV_RDB1_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s);assert not re.search(r'^import .*XR',s,re.M)
 sha=hashlib.sha256(p.read_bytes()).hexdigest();mod=str(p.relative_to(P))[:-5]
 match=[x for x in lean if x['module']==mod and x['source_sha256']==sha and x['exit']==0];assert match,('no final successful source receipt',mod)
 modules.append(dict(module=mod,sha256=sha,receipt=str(match[-1]['id'])+'-receipt.json'))
for n in [54738,54739]:
 j=next(x for x in lean if x['id']==n);assert j['exit']==0
assert len(next(x for x in lean if x['id']==54739)['print_axioms'])==10
for row in rows:
 if row['status']=='RESTORED':
  p=E/row['structural'];assert p.exists(),p
  for q in row.get('lean',[]):assert json.loads((E/q).read_text())['exit']==0
assert json.loads((E/'final-source-manifest.json').read_text())['ok']
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
changed=subprocess.check_output(['git','diff','--name-only','6273e6206164ac60fbc68a49fa888f98b87476f1','HEAD'],text=True).splitlines()
assert all(p.startswith(('evidence/pv-rdb1-20261028/','tools/pv-rdb1-20261028/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDB1_')) for p in changed),changed
j=dict(restored=restored,findings=findings,suspended=[],Lean_attempts=len(lean),Lean_ids=[x['id'] for x in lean],Lean_failed_attempts=[x['id'] for x in lean if x['exit']!=0],Lean_remaining=100-len(lean),native_scopes=len(native),native_remaining=120-len(native),native_failed_gates=[p.parent.name for p in sorted(E.glob('*/receipt.json')) if json.loads(p.read_text())['exit']!=0],kani=0,axioms=sorted(axioms),native_max_peak_RSS_KiB=max(int(x['peak_rss_kib']) for x in native),lean_max_peak_RSS_KiB=max(x['peak_rss_kib'] for x in lean),swap=0,final_modules=modules,combined_audit='54738-receipt.json',focused_all_ten_replay='54739-receipt.json',failed_replay_superseded='54799: incorrect unapplied local-binder proof terms; changed application compiled at54739',large_files=[],implementation_paths_changed=[],target='NOT YET ESTABLISHED',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scope='Ten existing qualified source/library native associations restored; two checked obstructions to unqualified full Result/effect promotion. No privacy endpoint or native-machine adequacy claimed.',new_trust_items=[])
(E/'audit.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:v for k,v in j.items() if k not in ['final_modules','Lean_ids']},indent=2))
