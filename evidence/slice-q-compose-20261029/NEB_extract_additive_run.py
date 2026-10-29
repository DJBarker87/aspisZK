#!/usr/bin/env python3
"""One serial reference extraction, using the unchanged scoped runner."""
from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029';H='dombarker@100.108.41.90';a=sys.argv[1] if len(sys.argv)>1 else 'NEB_E003';active=E/'NEB_ACTIVE.json'
assert not active.exists() and not (E/a).exists();active.write_text(json.dumps(dict(attempt=a,kind='extraction')))
def ssh(code,stdin=None,submitted=False):
 for attempt in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NEB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,transport_retry=attempt,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if attempt<10:time.sleep(60)
 raise SystemExit('transport exhausted before extraction launch or during read-only recovery')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFz_reservation.py',str(b/{(a+'-admission.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  if retry<10:time.sleep(60);continue
  raise SystemExit('transport exhausted before extraction launch')
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('missing extraction admission JSON')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,reservation=ad),indent=1)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('extraction admission wait',flush=True);time.sleep(180);continue
 raise SystemExit('STOP extraction admission')
cfg=dict(attempt=a,kind='extract',sources=['NEB_extract_additive.py','NEB_additive_reference.rs'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,command=['python3','NEB_extract_additive.py'],timeout=180,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3'},deps_fingerprint={'NCO_pins':'Charon daad69be, Aeneas c0cf4fcc'},expected_time='Optimized standalone fixed-array reference extraction; no field multiplication or corpus replay')
files={n:(E/n).read_text() for n in cfg['sources']};files[a+'.json']=json.dumps(cfg)
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
''');assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
r=ssh('cd '+B+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
# Never resubmit after this point. Transport recovery is read-only.
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list((b/{a!r}).rglob('*'))+list((b/'NEB_additive_extracted').rglob('*.lean'))+[b/'NEB_ADDITIVE_EXTRACTION_PINS.json']
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}))
''')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'NEB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print((E/a/'stdout.log').read_text()[-1800:]);sys.exit(rc['exit_status'])
