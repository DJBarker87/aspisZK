#!/usr/bin/env python3
"""Collect existing focused local logs; does not execute Lean or build tools."""
import hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[3]
dest=pathlib.Path(__file__).resolve().parent
base=root/'tools/pv-runjoin-20261026/local-proof'
packages=pathlib.Path('/Users/dominic/ZK/AspisFormal/.lake/packages')
paths=[base/'objects',base/'backend-cache']+[p/'.lake/build/lib/lean' for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
old_exits={20962:1,20963:0,20964:1,20966:1,20967:0,20968:1,20969:1,20973:0,20974:1,20975:0}
for log in sorted(dest.glob('out-*.log')):
    a=int(log.stem.split('-')[1]);raw=log.read_text()
    snapshots=list(dest.glob(f'{a}-*.lean.txt'));assert len(snapshots)==1,(a,snapshots)
    snap=snapshots[0];source=snap.read_bytes()
    exits=re.findall(r'^exit=(-?\d+)$',raw,re.M)
    code=int(exits[-1]) if exits else old_exits[a]
    deps={}
    for dep in re.findall(r'^import\s+(\S+)',source.decode(),re.M):
        found=next((p/(dep.replace('.','/')+'.olean') for p in paths if (p/(dep.replace('.','/')+'.olean')).exists()),None)
        if found:
            deps[dep]={'object_sha256':hashlib.sha256(found.read_bytes()).hexdigest(),'path':str(found.relative_to(root)) if found.is_relative_to(root) else str(found)}
        else:deps[dep]={'missing':True}
    time=re.search(r'^\s*([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys$',raw,re.M)
    rss=re.search(r'^\s*(\d+)\s+maximum resident set size$',raw,re.M)
    swaps=re.search(r'^\s*(\d+) swaps$',raw,re.M)
    axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",raw)
    record=dict(attempt=a,target='R1Z/'+snap.name.split('-',1)[1][:-9],source_revision='fed15c4bc5 (working source snapshot)',
        source_sha256=hashlib.sha256(source).hexdigest(),source_snapshot=snap.name,exit=code,
        wall_seconds=float(time[1]) if time else None,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(swaps[1]) if swaps else None,
        print_axioms=axioms,accepted=code==0 and not any('sorryAx' in x for x in axioms),
        command=['lake','env','lean','-M7000']+(['--root='+str(root/'docs/research/v8-r0-zk-20261009/lean')] if a>=20975 and a!=20978 else [])+(['-o',str(base/'objects'/'R1Z'/(snap.name.split('-',1)[1][:-9]+'.olean'))] if a>=20974 and a!=20978 else [])+[str(root/'docs/research/v8-r0-zk-20261009/lean'/'R1Z'/snap.name.split('-',1)[1][:-4])],
        lean_githash='8c9756b28d64dab099da31a4c09229a9e6a2ef35',mathlib_git='81a5d257c8e410db227a6665ed08f64fea08e997',
        environment='local focused new module; empty local Lake package; existing read-only mathlib and copied J/backend cache; no dependency build',
        resource_policy='local small-focused exception; Lean -M7000, measured peak RSS/swap. No local systemd scope is claimed.',
        direct_dependencies_postrun=deps,postrun_dependency_fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest())
    (dest/f'receipt-{a}.json').write_text(json.dumps(record,indent=2)+'\n')
print('collected',len(list(dest.glob('receipt-*.json'))),'local receipts')
