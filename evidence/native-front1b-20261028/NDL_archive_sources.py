"""Recover existing source evidence read-only; no build or resubmission."""
from pathlib import Path
import subprocess,json,hashlib,time,lzma
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028')
files={str(p.relative_to(b)):p.read_text() for d in b.glob('NDL_K[0-9][0-9][0-9]') for p in (d/'sources').rglob('*.rs') if p.is_file()}
pins={str(p.relative_to(b)):p.read_text() for d in b.glob('NDL_K[0-9][0-9][0-9]') for p in (d/'sources').rglob('NDL_SOURCE_PINS.json')}
print(json.dumps(dict(files=files,pins=pins)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NDL_ARCHIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);old=E/'NDL_SOURCE_ARCHIVE.json';compressed=E/'NDL_SOURCE_ARCHIVE.json.xz';index=json.loads(old.read_text() if old.exists() else lzma.decompress(compressed.read_bytes()).decode())['source_files'] if old.exists() or compressed.exists() else {};out=E/'NDL_SOURCE_ARCHIVE';out.mkdir(exist_ok=True)
# Include local extraction reference snapshots; preserve original receipt hashes.
for p in E.glob('NDL_*/sources/**/*.rs'):
 x['files']['local/'+str(p.relative_to(E))]=p.read_text()
for n,s in x['files'].items():
 h=hashlib.sha256(s.encode()).hexdigest();dest=out/(h+'.patch');lines=s.splitlines(True)
 if not dest.exists():dest.write_text('--- /dev/null\n+++ b/'+Path(n).name+'\n@@ -0,0 +1,'+str(len(lines))+' @@\n'+''.join('+'+l for l in lines))
 index[n]=dict(sha256=h,patch=str(dest.relative_to(E)),bytes=len(s.encode()))
(E/'NDL_SOURCE_ARCHIVE.json').write_text(json.dumps(dict(source_files=index,historical_source_pinsets=x['pins'],representation='new-file patches; hashes refer to reconstructed original UTF-8 source bytes'),indent=2)+'\n')
for p in E.glob('NDL_*/sources/**/*.rs'):p.unlink()
target=E/'NDL_SOURCE_ARCHIVE.json'
if target.stat().st_size>20*1024*1024:
 raw=target.read_bytes();target.with_suffix('.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  '+target.name+'\n');target.with_suffix('.json.xz').write_bytes(lzma.compress(raw,preset=6));target.unlink()
print(json.dumps(dict(source_paths=len(index),unique_sources=len(list(out.glob('*.patch'))),pinsets=len(x['pins']))))
