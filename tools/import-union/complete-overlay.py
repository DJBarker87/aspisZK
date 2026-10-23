#!/usr/bin/env python3
"""Complete namespace packages in a private overlay with read-only cache links.

Lean can resolve a namespace to its first directory before looking for a sibling
module. Never create links at planned build outputs: compiling through a link
could replace a shared object. Existing outputs must be regular private files.
"""
import hashlib
import json
from pathlib import Path
W = Path(__file__).resolve().parent
plan = json.loads((W/'plan.json').read_text())
objects = W/'objects'
targets = {r['module'] for r in plan['ordered']}
providers = {}
for root in map(Path, plan['lean_paths']):
    for p in root.rglob('*.olean'):
        if p.is_file():
            providers.setdefault(str(p.relative_to(root))[:-6].replace('/','.'),p)
links=[]
for m,p in sorted(providers.items()):
    dest = objects/(m.replace('.','/')+'.olean')
    if m in targets:
        assert not dest.is_symlink(), 'build output is a shared-cache link: '+str(dest)
        continue
    if dest.is_symlink():
        assert dest.resolve()==p.resolve(), (dest,p)
    elif dest.exists():
        raise RuntimeError('unexpected private non-target object '+str(dest))
    else:
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(p)
    # Preserve companion artifacts when present in a pinned cache.
    for companion, target in [(Path(str(p)+s),Path(str(dest)+s)) for s in ['.private','.server']] + [(p.with_suffix('.ir'),dest.with_suffix('.ir'))]:
        if companion.is_file():
            if target.is_symlink():
                assert target.resolve()==companion.resolve(), target
            elif target.exists():
                raise RuntimeError('unexpected companion '+str(target))
            else:
                target.symlink_to(companion)
    links.append({'module':m,'provider':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(W/'evidence/overlay-links.json').write_text(json.dumps(links,indent=2)+'\n')
print('created',len(links),'unchanged-cache links; excluded',len(targets),'build outputs')
