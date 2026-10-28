from NBZ_host import *
import sys,hashlib
attempt=sys.argv[1]
r=py(f'''from pathlib import Path
import json
b=Path({B!r})/{attempt!r}
print(json.dumps({{n:(b/n).read_text() for n in ['receipt.json','stdout.log','time.log'] if (b/n).is_file()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/attempt/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if 'receipt.json' not in out:raise SystemExit('submitted receipt unresolved: recover read-only, never resubmit')
rc=json.loads(out['receipt.json']);existing=[json.loads(l)['attempt'] for l in (E/'NBZ_ATTEMPTS.jsonl').read_text().splitlines()]
if attempt not in existing:
 with (E/'NBZ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
r=ssh('sha256sum '+B+'/NBZ_src/Cargo.lock');assert r.returncode==0
checkpath=E/(attempt+'-graph-check.json');check=json.loads(checkpath.read_text());check['lock_after_sha256']=r.stdout.split()[0];check['lock_unchanged']=check['lock_after_sha256']==check['lock_before_sha256'];assert check['lock_unchanged'];check['recovered_read_only']=True;checkpath.write_text(json.dumps(check,indent=2)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print(out['stdout.log'][-1800:])
