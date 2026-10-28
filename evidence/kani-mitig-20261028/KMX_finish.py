from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
import KMX_host as h
payload=json.loads((E/'KMX_all_payload.json').read_text())
expected={n:hashlib.sha256(v.encode()).hexdigest() for n,v in payload.items() if not Path(n).stem.startswith('KMX_')}
r=h.remote_py('''from pathlib import Path
import hashlib,json,subprocess,shutil,re
b=Path('''+repr(h.B)+''');s=b/'KMX_src'
live=[x for x in subprocess.check_output(['ps','-eo','args='],text=True).splitlines() if re.match(r'^python3 S2W_(?:run|lean)_host[.]py KMX_',x.strip())]
assert not live,live
pins=json.loads((b/'KMX_FROZEN_SOURCE_PINS.json').read_text());expected='''+repr(expected)+'''
changed={n:hashlib.sha256((s/n).read_bytes()).hexdigest() for n,sha in pins.items() if hashlib.sha256((s/n).read_bytes()).hexdigest()!=sha}
assert all(n in expected and expected[n]==sha for n,sha in changed.items()),changed
assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==sha for n,sha in expected.items())
initial=json.loads((b/'KMX_INITIAL_HOST_PINS.json').read_text());final={};bad=[]
for label,root in [('cache','''+repr(h.CACHE)+'''),('coherent','''+repr(h.C+'/objects')+''')]:
 now={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}
 final[label]=dict(objects=now,added=sorted(set(now)-set(initial[label])))
 bad.extend(n for n,v in initial[label].items() if now.get(n)!=v)
assert not bad,bad
removed=[]
for n in ['KMX_target','KMX_tmp']:
 p=b/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
for n in ['KMX_native_bin','KMX_native_extra_bin']:
 p=b/n
 if p.is_file():p.unlink();removed.append(str(p))
for p in b.glob('KMX_latest_probe*'):
 if p.suffix!='.rs' and p.is_file():p.unlink();removed.append(str(p))
assert Path('''+repr(h.CACHE)+''').is_dir()
out=dict(source_files_checked=len(pins),changed_scratch_parents=changed,expected_overlay_hashes=expected,lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),lock_is_symlink=(s/'Cargo.lock').is_symlink(),preexisting_object_changes=bad,objects=final,live_own_scopes=live,removed_rebuildable_scratch=removed,persistent_cache_retained=True,keys_touched=False,disk_free_bytes=shutil.disk_usage(b).free)
(b/'KMX_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
''')
assert r.returncode==0,r.stderr
(E/'KMX_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
local=subprocess.check_output(['git','diff','--name-only','ee6fb599d9','--','crates','programs'],text=True)
assert not local,local
print('Scratch source and preexisting object audit PASS; own targets removed; persistent cache retained')
