#!/usr/bin/env python3
"""Collect compact receipts; large derived JSON is hash/size/script only."""
import hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
H='/home/dombarker/project-offloads/codex-cx-s10-inventory4-20261021';REMOTE='dombarker@100.108.41.90'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(remote,local):
    subprocess.run(['scp','-q',REMOTE+':'+H+'/'+remote,str(local)],check=True,timeout=60)
for filename in ['receipt.json','time.log','stdout.log','stderr.log']:
    fetch('instances-host-receipt/'+filename,E/('instances-host-'+filename))
for name in ['instances','indirect','cfg']:
    p=Path('/tmp')/('s10-pass4-'+name+'.json');fetch(name+'.json',p)
    pin=dict(path=H+'/'+name+'.json',sha256=sha(p),bytes=p.stat().st_size,generator='tools/s10-inventory4-20261021/'+('instances-host.py' if name=='instances' else name+'-host.py'))
    (E/(name+'-pin.json')).write_text(json.dumps(pin,indent=2)+'\n')
    x=json.loads(p.read_text())
    if name=='instances':
        # Existing observations are already pinned in pass three. Retain only
        # the exact added trait matches plus one summary for every declaration.
        reduced=[]
        prior={mode:{r['id']:r for r in json.loads((B/'evidence/s10-inventory3-20261021'/('frontiers-'+mode+'.json')).read_text())} for mode in ['default','devnet','pool']}
        for r in x['records']:
            old=prior[r['mode']][r['id']];seen={(o['path'],o['line']) for o in old['compiler_occurrences']}
            extra=[o for o in r['observations'] if (o['path'],o['line']) not in seen]
            reduced.append({k:v for k,v in r.items() if k not in ['observations','mono_records','generic_body']}|dict(
                prior_observations=len(old['compiler_occurrences']),prior_mono_records=len(old['monomorphizations']),
                frozen_body_count=len(r['generic_body']),added_observations=extra,total_observations=len(r['observations'])))
        x['records']=reduced;x['full_derived_json']=pin
    raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
    if len(raw)<=5_000_000:(E/(name+'.json')).write_bytes(raw)
    print(name,pin['bytes'],len(raw),x.get('counts'))
