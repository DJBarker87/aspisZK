"""Own serial extraction/fidelity client; unchanged admitted S2W host runner."""
from NEW_remote import *
import sys,shlex,hashlib,lzma,base64
R=E.parent.parent
a,kind=sys.argv[1:]
assert kind=='extract' and a.startswith('NEW_E') and 1<=int(a[-3:])<=10
active=E/'NEW_ACTIVE.json';assert not active.exists() and not (E/a).exists()
active.write_text(json.dumps(dict(attempt=a,kind=kind)))
admit(a)
code=f'''from pathlib import Path
import json
b=Path({B!r});s=b/'NEW_src'
print(json.dumps(['NEW_src/'+str(p.relative_to(s)) for p in (s/'crates/aspis-core').rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']]))
'''
r=ssh(a,'python3',code);assert r.returncode==0,r.stderr
sources=['NEW_extract_actual.py','NEW_TOOL_PINS.json','NEW_SOURCE_PINS.json','NEW_src/Cargo.lock','NEW_src/Cargo.toml']+json.loads(r.stdout)
cfg=dict(attempt=a,kind=kind,target='aspis_core::field::M31::inv',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=sources,command=['python3','NEW_extract_actual.py'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OPT_LEVEL='3'),deps_fingerprint=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),expected_time='Optimized core-only compilation and direct actual-body Charon/Aeneas extraction; no multiplication in Kani')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
upload(a,{'NEW_extract_actual.py':(E/'NEW_extract_actual.py').read_text(),a+'.json':json.dumps(cfg)})
r=ssh(a,'cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# No resubmission. All later operations only recover retained outputs.
r=ssh(a,'python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});paths=list((b/{a!r}).rglob('*'))+list((b/'NEW_actual_extracted').rglob('*.lean'))+[b/'NEW_ACTUAL_EXTRACTION_PINS.json',b/'NEW_InverseActual.llbc']+list((b/'NEW_inverse_extract').glob('Cargo.*'))+list((b/'NEW_inverse_extract/src').glob('*.rs'))
out={{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}
data=json.dumps(out,sort_keys=True).encode();print(json.dumps(dict(sha256=hashlib.sha256(data).hexdigest(),data=base64.b64encode(lzma.compress(data,preset=6)).decode())))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout);raw=base64.b64decode(out['data']);plain=lzma.decompress(raw);assert hashlib.sha256(plain).hexdigest()==out['sha256']
(E/(a+'_OUTPUTS.json.xz')).write_bytes(raw);(E/(a+'_OUTPUTS.json.sha256')).write_text(out['sha256']+'\n')
for name,text in json.loads(plain).items():
 if name.endswith('.llbc') or '/sources/' in name:continue
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'NEW_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print((E/a/'stdout.log').read_text()[-2000:]);sys.exit(rc['exit_status'])
