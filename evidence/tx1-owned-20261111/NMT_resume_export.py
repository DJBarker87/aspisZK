"""Export passing objects in one admitted capped inspection, then recover hashes."""
from NMT_formal import run,E,B,ssh
import json
rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
n=max(int(r['attempt'][5:])for r in rows if r.get('attempt','').startswith('NMT_L')and'exit_status'in r)+1
assert n<=310
rc=run(f'NMT_L{n:03}','inspect','resume-export',command=['python3','NMT_resume_export_host.py'],extra={n:(E/n).read_text()for n in ['NMT_resume_export_host.py','NMT_RESUME_MODULES.json']})
assert rc['exit_status']==0
names=['NMT_RESUME_EXPORT.json','NMT_RESUME_AENEAS_PINS.json','NMT_RESUME_RETENTION.json']
r=ssh('python3',f"from pathlib import Path;import json;print(json.dumps({{n:(Path({B!r})/n).read_text()for n in {names!r}}}))")
assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
