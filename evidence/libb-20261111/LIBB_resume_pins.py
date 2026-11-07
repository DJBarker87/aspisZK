"""Rehash this continuation's selected input objects and retained exports."""
from pathlib import Path
import json,hashlib,lzma,subprocess,time
E=Path(__file__).resolve().parent;expected={}
for p in E.glob('LIBB_L3[0-9][0-9]/receipt.json'):
 if int(p.parent.name[-3:])<301:continue
 r=json.loads(p.read_text())
 for name,x in r['deps_fingerprint']['selected_objects'].items():
  if name in expected:assert expected[name]==x['sha256'],name
  expected[name]=x['sha256']
for n in ['LIBB_BUNDLE_REUSE.json','LIBB_BUNDLE_DEPS_REUSE.json']:
 for x in json.loads((E/n).read_text())['files']:
  expected[x['source']]=x['sha256'];expected[x['destination']]=x['sha256']
export=json.loads((E/'LIBB_EXPORT.json').read_text())
for x in export['objects']:expected[x['path']]=x['sha256']
code='''import json,hashlib,shutil
from pathlib import Path
expected=json.loads(%r);rows=[]
for name,h in sorted(expected.items()):
 p=Path(name);actual=hashlib.sha256(p.read_bytes()).hexdigest()
 assert actual==h,(name,h,actual)
 rows.append(dict(path=name,sha256=actual,bytes=p.stat().st_size))
print(json.dumps(dict(objects=rows,lean_path=%r,disk=shutil.disk_usage('/home/dombarker/project-offloads/codex-cx-libb-20261111')._asdict(),deletions=0)))
'''%(json.dumps(expected),json.loads((E/'LIBB_EXPORT_PATHS.json').read_text()))
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/'LIBB_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(event='resume_pins',retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['disk']['free']>=40_000_000_000
raw=(json.dumps(x,indent=1)+'\n').encode()
(E/'LIBB_RESUME_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'LIBB_RESUME_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(objects=len(x['objects']),free=x['disk']['free'],deletions=0)))
