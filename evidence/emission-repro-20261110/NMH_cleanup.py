#!/usr/bin/env python3
"""Remove only this job's rebuildable Cargo output after terminal recovery.
The assigned persistent Lean cache, sources, raw emissions, receipts and LLBC
are retained. No keys or wallets are created or removed by this job.
"""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-emission-repro-20261110';H='dombarker@100.108.41.90'
assert len(list(E.glob('NMH_E*/receipt.json')))==30,'all scopes must be terminal'
post=json.loads((E/'NMH_HOST_POSTCHECK.json').read_text());assert not post['source_drift'] and not post['owned_processes']
code='''from pathlib import Path
import shutil,json,os
b=Path(%r);p=b/'NHR_target';assert str(b.resolve())==%r
assert not p.is_symlink(),'never follow a cache link'
removed=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()) if p.exists() else 0
if p.exists():shutil.rmtree(p)
print(json.dumps(dict(removed_directory=str(p),removed_bytes=removed,persistent_Lean_cache_touched=False,retained_sources_emissions_LLBC_receipts=True,remaining_owned_bytes=sum(os.stat(os.path.join(d,n)).st_size for d,ds,ns in os.walk(b) for n in ns),free_bytes=shutil.disk_usage(b).free)))
'''%(B,B)
for n in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 with (E/'NMH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(step='owned Cargo-output cleanup',retry=n,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if n<10:time.sleep(60)
assert r.returncode==0,r.stderr
# Removal is idempotent and confined to a verified non-symlink generated-output path.
d=json.loads(r.stdout);(E/'NMH_HOST_CLEANUP.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
