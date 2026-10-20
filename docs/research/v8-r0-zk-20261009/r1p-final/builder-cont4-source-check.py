#!/usr/bin/env python3
"""Check the isolated host's exact crate/proof sources and lock identities."""
from pathlib import Path
import subprocess,json,hashlib,tomllib
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
roots=['crates/aspis-core','crates/aspis-statement','tools/r1-builder-reference',
 'docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters',
 'docs/research/v8-r0-zk-20261009/refine/poseidon']
pins={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
 for root in roots for p in (ROOT/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml','.lock']}
script='''import pathlib,hashlib,json
s=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021/source')
pins=PP
print(json.dumps({'pins':{p:hashlib.sha256((s/p).read_bytes()).hexdigest() if (s/p).exists() else 'missing' for p in pins},'lock':(s/'Cargo.lock').read_text()}))
'''.replace('PP',repr(pins))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
diffs={p:{'local':v,'host':remote['pins'][p]} for p,v in pins.items() if remote['pins'][p]!=v}; assert not diffs,diffs
key=lambda p:(p['name'],p['version'])
a={key(p):p for p in tomllib.loads((ROOT/'Cargo.lock').read_text())['package']}
b={key(p):p for p in tomllib.loads(remote['lock'])['package']}
assert not (set(b)-set(a)),'unexpected host lock package/version'
for k,p in b.items():
 assert (p.get('source'),p.get('checksum'))==(a[k].get('source'),a[k].get('checksum')),k
out={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'source_dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()),
 'rust_source_base':'5f877a406; shipped crate source byte-unchanged throughout this continuation',
 'pins':pins,'diffs':diffs,'workspace_adapter':'Host top-level Cargo.toml narrows workspace membership; cargo prunes unused lock packages/features and version disambiguators.',
 'lock_comparison':{'repo_sha256':hashlib.sha256((ROOT/'Cargo.lock').read_bytes()).hexdigest(),
 'host_sha256':hashlib.sha256(remote['lock'].encode()).hexdigest(),
 'host_package_count':len(b),'repo_package_count':len(a),'host_extra_packages':[],
 'all_shared_source_and_checksum_identities_equal':True,
 'pruned_package_count':len(set(a)-set(b)),
 'changed_dependency_records':[str(k) for k,p in b.items() if p!=a[k]]},
 'receipt_revision_labels':'Original private capped.py labels are retained verbatim, including inherited historical labels. Crate source base plus exact per-run proof-source/tool hashes supply corrected reproducible provenance; no old label is treated as source identification.'}
(HERE/'builder-cont4-evidence/source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS:',len(pins),'exact host crate/proof file pins; lock package versions/source checksums agree')
