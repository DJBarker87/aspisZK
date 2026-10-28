from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
import KMX_host as h
h.admit(sys.argv[1])
r=h.remote_py('''from pathlib import Path
import json,hashlib
p=Path('''+repr(h.B+'/KMX_src/Cargo.lock')+''');data=p.read_bytes();was_symlink=p.is_symlink()
assert hashlib.sha256(data).hexdigest()=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
if was_symlink:p.unlink();p.write_bytes(data)
print(json.dumps(dict(was_symlink=was_symlink,is_symlink=p.is_symlink(),sha256=hashlib.sha256(p.read_bytes()).hexdigest())))''')
assert r.returncode==0,r.stderr
(E/'KMX_LOCK_MATERIALIZATION.json').write_text(r.stdout)

payload={
 'KMX_gate.py':(E/'KMX_gate.py').read_text(),
 'KMX_latest_install.py':(E/'KMX_latest_install.py').read_text(),
 'KMX_LATEST_RELEASE.json':(E/'KMX_LATEST_RELEASE.json').read_text(),
 'KMX_latest_probe.rs':(E/'KMX_latest_probe.rs.input').read_text(),
 'KMX_native_extra.rs':(E/'KMX_native_extra.rs.input').read_text(),
 'KMX_src/crates/aspis-r1-cost-probe/src/KMX_trigger.rs':(E/'KMX_trigger.rs.txt').read_text(),
}
for name,text in payload.items():
 r=h.remote_py('from pathlib import Path\np=Path('+repr(h.B+'/'+name)+')\np.write_text('+repr(text)+')')
 assert r.returncode==0,r.stderr
extra=json.loads((E/'KMX_EXTRA_SOURCES.json').read_text())
extra=list(dict.fromkeys(extra+list(payload)))
(E/'KMX_EXTRA_SOURCES.json').write_text(json.dumps(extra,indent=2)+'\n')
print('uploaded final inputs:',len(payload))
