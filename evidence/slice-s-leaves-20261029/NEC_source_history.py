"""Reconstruct every persistent native scratch source-pin manifest, without replay."""
from pathlib import Path
import subprocess,json,hashlib,re,tempfile,lzma
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 return p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
pins=json.loads((E/'NEC_NATIVE_SOURCE.json').read_text())['source_sha256']
initial=dict(pins);rows=[];frozen={};latest={}
for line in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines():
 rc=json.loads(line)
 if rc['kind']!='kani':continue
 a=rc['attempt'];patch=raw(E/a/'NEC_harness.patch')
 with tempfile.TemporaryDirectory(prefix='NEC-source-history-') as tmp:
  root=Path(tmp)
  for name in re.findall(r'^--- a/(.+)$',patch.decode(),re.M):
   if name not in frozen:frozen[name]=subprocess.check_output(['git','show','4bb3b3f5:'+name])
   p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(frozen[name])
  subprocess.run(['git','apply','--unsafe-paths','-'],input=patch,cwd=root,check=True,capture_output=True)
  updated=[]
  for name in [name[len('NEC_src/'):] for name in rc['source_hashes'] if name.startswith('NEC_src/') and name.endswith('.rs')]:
   q=root/name
   if not q.exists():
    if name not in frozen:frozen[name]=subprocess.check_output(['git','show','4bb3b3f5:'+name])
    data=frozen[name]
   else:data=q.read_bytes()
   assert sha(data)==rc['source_hashes']['NEC_src/'+name],(a,name)
   pins[name]=sha(data);latest[name]=a;updated.append(name)
 manifest=json.dumps(pins,indent=1).encode();actual=sha(manifest);expected=rc['source_hashes']['NEC_SOURCE_PINS.json']
 assert actual==expected,(a,'persistent source-pin hash differs',actual,expected)
 inherited={p:dict(sha256=h,last_updated=latest.get(p,'setup')) for p,h in pins.items() if h!=initial.get(p) and p not in updated}
 rows.append(dict(attempt=a,source_pins_sha256=actual,source_entries=len(pins),source_pin_hash_exact=True,inherited_instrumented_sources=inherited))
(E/'NEC_SOURCE_HISTORY.json').write_text(json.dumps(dict(initial_pin_manifest_sha256=sha(json.dumps(initial,indent=1).encode()),all_recorded_source_pin_hashes_exact=True,attempts=rows,conclusion='Earlier manifests are reproducible exactly. Old unused module overlays are explicit here; new runner resets every touched frozen entry file before each attempt.'),indent=1)+'\n')
print('Exact persistent source-pin histories',len(rows))
