"""Lane-owned extraction client, unchanged S2W runner, serial admission."""
from NFG_remote import *
import sys,shlex,hashlib,lzma,base64
R=E.parent.parent;a=sys.argv[1]
assert a.startswith('NFG_E') and 1<=int(a[-3:])<=10
assert not (E/a).exists();active=E/'NFG_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,kind='extract')))
admit(a)
sources=['NFG_extract_row.py','NFG_TOOL_PINS.json','NFG_src/Cargo.lock','NFG_src/crates/aspis-core/src/field.rs','NFG_src/crates/aspis-core/src/r0/domain.rs']
cfg=dict(attempt=a,kind='extract',target='actual frozen field negation/zero methods',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=sources,command=['python3','NFG_extract_row.py'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OPT_LEVEL='3'),deps_fingerprint=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pins='NCO_EXTRACTION_PINS.json'),expected_time='Optimized compilation then row local-G extraction; multiplication never called')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
upload(a,{n:(E/n).read_text() for n in ['NFG_extract_row.py']}|{a+'.json':json.dumps(cfg)})
r=ssh(a,'cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh(a,'python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});paths=list((b/{a!r}).rglob('*'))+list((b/'NFG_row_extracted').rglob('*.lean'))+[b/'NFG_ROW_EXTRACTION_PINS.json',b/'NFG_frozen.llbc']+list((b/'NFG_row_ref').glob('Cargo.*'))+list((b/'NFG_row_ref/src').glob('*.rs'))
out={{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}
data=json.dumps(out,sort_keys=True).encode();print(json.dumps(dict(sha256=hashlib.sha256(data).hexdigest(),data=base64.b64encode(lzma.compress(data,preset=6)).decode())))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout);raw=base64.b64decode(out['data']);plain=lzma.decompress(raw);assert hashlib.sha256(plain).hexdigest()==out['sha256']
(E/(a+'_OUTPUTS.json.xz')).write_bytes(raw);(E/(a+'_OUTPUTS.json.sha256')).write_text(out['sha256']+'\n')
for name,source in json.loads(plain).items():
 if name.endswith('.llbc') or '/sources/' in name:continue
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source)
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'NFG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print((E/a/'stdout.log').read_text()[-2000:]);sys.exit(rc['exit_status'])
