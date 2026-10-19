#!/usr/bin/env python3
"""Collect the pinned constraint repair build and scoped regression evidence."""
from pathlib import Path
import hashlib,json,subprocess
here=Path(__file__).resolve().parent;area=here.parents[1]
out=area/'evidence/cu-equivalence-20261019/trait-constraints-diagnostic-a';out.mkdir(exist_ok=False)
root='/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019'
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=10']
for name in ['trait-constraints.patch','build.sh','preflight.json','receipt.json','compile-time.log','compile.log','version.txt','controller-source.py']:
    target=out/'build'/name;target.parent.mkdir(exist_ok=True)
    subprocess.run(['scp',*opts,host+':'+root+'/aeneas-trait-constraints/'+name,str(target)],check=True)
subprocess.run(['scp',*opts,'-r',host+':'+root+'/trait-constraints-regression-a',str(out/'regression')],check=True)
recheck=out/'reservation-recheck';recheck.mkdir()
for name in ['receipt.json','preflight.json','compile-time.log','compile.log','version.txt']:
    subprocess.run(['scp',*opts,host+':'+root+'/aeneas-trait-constraints-reservation-checked/'+name,str(recheck/name)],check=True)
files={str(p.relative_to(out)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
    for p in out.rglob('*') if p.is_file()}
manifest=dict(status='FULL_NORMALIZED_CRATE_BORROW_CHECKED_DICTIONARY_ADMISSION_OPEN',files=files,
    resource_review=dict(original_build='Aggregate container admission was not established; original outer reservations plus compile cap projected 56.375GiB. Evidence retained as a resource-policy exception, not a compliant launch.',
        replacement='Same source and same binary hash rechecked with 1GiB controller, 8GiB compiler, explicit actual aggregate gate and continuous reservation monitoring.'),
    source_traits='array-library-diagnostic-a/try-trait.rs',
    preserved=['All source trait clauses and type constraints','Exact full instantiated projection matching',
        'Ordinary input-type checks after normalization','Borrow/copy/sanity checks','Original fixed-point iteration limit'],
    open=['Experimental dereference-rewrite admission','Generic productive dictionary/source mapping',
        'Unsafe primitive admission','Library builder/caller composition','Whole verifier and soundness/privacy transfers'])
(out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status=manifest['status'],files=len(files))))
