from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb1-20261028'
expected=set('V164 V170 V178 V181 V182 V183 V184 V186 V187 V195 V198 V219'.split())
rows=[json.loads(p.read_text()) for p in (E/'rows').glob('*.json')];assert {x['row'] for x in rows}==expected
assert [x['row'] for x in rows if x['status']=='RESTORED']==['V186']
native=[json.loads(p.read_text()) for p in E.glob('*/receipt.json')];assert len(native)==20 and all(x['exit']==0 and int(x['swap'])==0 for x in native)
lean=[json.loads((E/f'{n}-receipt.json').read_text()) for n in [54700,54701,54797,54798]]
for receipt in lean:
 assert receipt['exit']==0 and receipt['swap']==0
 for line in receipt['print_axioms']:
  m=re.search(r'axioms: \[([^]]*)\]',line)
  if m:assert set(x.strip() for x in m[1].split(',') if x.strip())<=set(['propext','Classical.choice','Quot.sound'])
 for path in [R/'docs/research/v8-r0-zk-20261009/lean'/ (receipt['module']+'.lean')]:
  # 54700 is deliberately superseded by the changed 54701 source.
  if receipt['id']!=54700:assert hashlib.sha256(path.read_bytes()).hexdigest()==receipt['source_sha256']
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RDB1_*.lean'):
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',text);assert not re.search(r'^import .*XR',text,re.M)
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
changed=subprocess.check_output(['git','diff','--name-only','6273e6206164ac60fbc68a49fa888f98b87476f1','HEAD'],text=True).splitlines()
assert all(p.startswith(('evidence/pv-rdb1-20261028/','tools/pv-rdb1-20261028/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDB1_')) for p in changed),changed
j=dict(restored=['V186'],suspended=sorted(expected-{'V186'}),findings=[],Lean_attempts=4,Lean_ids=[54700,54701,54797,54798],native_scopes=20,kani=0,unused_audit_id=54799,axioms=['propext'],native_max_peak_RSS_KiB=max(int(x['peak_rss_kib']) for x in native),lean_max_peak_RSS_KiB=max(x['peak_rss_kib'] for x in lean),swap=0,large_files=[],forbidden_source_constructs=False,implementation_paths_changed=[],target='NOT YET ESTABLISHED',scope='V186 existing library/source native association only; unchanged original dictionary law reused by exact source equation, focused replay of the new bridge; no package-wide endpoint replay',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'audit.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
