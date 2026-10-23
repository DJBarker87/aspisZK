#!/usr/bin/env python3
"""Typed frozen MIR observations, with trait aliases matched explicitly.
No occurrence is promoted to final LLVM/ELF inline provenance.
"""
import hashlib,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023')
P=H.parent/'codex-cx-s10-repin2-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((P/'packet/frontiers-default.json').read_text())
result=[];pins=[]
for mode,build in [('default','build-default-v3'),('devnet','build-devnet-v2'),('pool','build-pool-v1')]:
    files=[]
    for p in sorted((P/build/'compiler-output').glob('*.mir')):
        pins.append(dict(mode=mode,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
        current=None;start=0
        for n,l in enumerate(p.read_text().splitlines(),1):
            if l.startswith('fn '):current=l;start=n
            if '(inlined ' in l or (' -> ' in l and '=' in l):
                files.append(dict(path=str(p),line=n,caller=current,caller_line=start,text=l.strip()))
    old={r['id']:r for r in json.loads((P/'packet'/('frontiers-'+mode+'.json')).read_text())}
    for row in rows:
        name=row['mir_name'];trait=None
        m=re.search(r'::<(.+) as (.+)>::([^:]+)$',name)
        if m:
            ty=m[1].rsplit('::',1)[-1];trait=m[2].rsplit('::',1)[-1];method=m[3]
            pattern=re.compile(r'<(?:[\w]+::)*'+re.escape(ty)+r' as (?:[\w]+::)*'+re.escape(trait)+r'>::'+re.escape(method)+r'(?=[(>) ])')
            extra=[x for x in files if pattern.search(x['text'])]
        else:extra=[]
        prior=old[row['id']];seen={(r['path'],r['line']):r for r in prior['compiler_occurrences']}
        for r in extra:seen.setdefault((r['path'],r['line']),r)
        obs=list(seen.values())
        # Preserve per-location identity; duplicate instance spellings across
        # crates/codegen units are never deduplicated into a fake unique body.
        result.append(dict(mode=mode,id=row['id'],declaration=name,
            generic_body=prior['frozen_bodies'],mono_records=prior['monomorphizations'],
            observations=sorted(obs,key=lambda r:(r['path'],r['line'])),
            additional_trait_alias_observations=len(extra),trait=trait,
            status='COMPILER_OBSERVED' if obs or prior['monomorphizations'] else 'BODY_ONLY',
            final_machine_inline_correspondence='OPEN',
            residual='A frozen generic body or MIR inline scope is not an ELF-reachable instantiated source execution. Final codegen provenance or a source-exclusion certificate is still required.'))
out=dict(schema='s10-pass4-frozen-instance-observations-v1',inputs=pins,records=result,
    counts=dict(records=len(result),additional_trait_alias_observations=sum(r['additional_trait_alias_observations'] for r in result),body_only=sum(r['status']=='BODY_ONLY' for r in result)),
    generator='tools/s10-inventory4-20261021/instances-host.py')
raw=(json.dumps(out,indent=2,sort_keys=True)+'\n').encode()
p=H/'instances.json';p.write_bytes(raw)
print(json.dumps(dict(counts=out['counts'],path=str(p),sha256=sha(p),bytes=len(raw))),flush=True)
