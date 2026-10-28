from pathlib import Path
import sys,json,hashlib,zlib,base64
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCE_host as h
initial=json.loads((E/'NCE_INITIAL_HOST_PINS.json').read_text())
rc=json.loads((E/'NCE_L003/receipt.json').read_text())
pins=initial['cache']
for obj in rc['deps_fingerprint']['selected_objects'].values():pins[obj['path']]={'sha256':obj['sha256']}
payload=base64.b64encode(zlib.compress(json.dumps(pins).encode())).decode()
r=h.remote_py(f'''from pathlib import Path
import hashlib,json,subprocess,re,zlib,base64
pins=json.loads(zlib.decompress(base64.b64decode({payload!r})))
bad=[]
for name,expected in pins.items():
 p=Path(name)
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected['sha256']:bad.append(name)
p=Path({(h.CACHE+'/NCE_ErrorObstruction.olean')!r})
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCE_',x.strip())]
print(json.dumps(dict(reused_objects_checked=len(pins),mismatches=bad,live_own_runners=live,new_object=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size))))
''')
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);assert not out['mismatches'] and not out['live_own_runners']
(E/'NCE_FINAL_OBJECT_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
