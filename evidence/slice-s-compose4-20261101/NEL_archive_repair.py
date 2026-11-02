"""Archive own accepted objects and clean only rebuildable own build scratch."""
from pathlib import Path
import json,subprocess,hashlib,time,sys,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose4-20261029';H='dombarker@100.108.41.90';a='NEL_ARCHIVE_REPAIR'
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NEL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP persistent transport')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print((b/{(a+'-barrier-'+str(retry)+'.log')!r}).read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP archive admission')
host="from pathlib import Path\nimport json,hashlib,shutil\nb=Path(__file__).resolve().parent\nold=json.loads((b/'NEL_CACHE_FINAL.json').read_text())\nsrc=Path(old['permanent_cache_retained']);dst=b.parent/'codex-cx-slice-s-compose4-cache-20261029/NEL_final_objects_20261102'\nassert src==b.parent/'codex-cx-slice-s-compose3-cache-20261029/NEL_final_objects_20261102'\nassert not dst.exists()\nexpected={Path(x['destination']).name:x for x in old['copied']}\nassert {p.name for p in src.iterdir()}==set(expected)\nfor n,row in expected.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==row['sha256']\nshutil.move(str(src),str(dst))\nassert not src.exists()\nfor row in old['copied']:\n row['destination']=str(dst/Path(row['destination']).name)\n assert hashlib.sha256(Path(row['destination']).read_bytes()).hexdigest()==row['sha256']\nold['permanent_cache_retained']=str(dst)\nold['archive_path_correction']=dict(accidental_owned_directory=str(src),corrected_owned_directory=str(dst),only_newly_created_NEL_files_moved=True,predecessor_original_files_modified=False)\n(b/'NEL_CACHE_FINAL.json').write_text(json.dumps(old,indent=1)+'\\n')\nprint(json.dumps(old['archive_path_correction']))\n"
cfg=dict(attempt=a,kind='archive',module='archive own accepted objects',sources=['NEL_archive_repair_host.py'],command=['python3','NEL_archive_repair_host.py'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin'))
files={'NEL_archive_repair_host.py':host,a+'.json':json.dumps(cfg)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n');(E/'NEL_archive_repair_host.py').write_text(host)
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log','NEL_CACHE_FINAL.json']!r} if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'submitted archive unresolved; never resubmit'
rc=json.loads(out[a+'/receipt.json']);entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=dict(path=str(E/a/'receipt.json'),sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest())
with (E/'NEL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
