#!/usr/bin/env python3
"""Local evidence identity/retention check only; no host or builds."""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-slab-20261024/go-api'
def digest(p):
    b=p.read_bytes();return dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def main():
    start=time.monotonic()
    host=json.loads((OUT/'live-command.json').read_text())
    for name,value in host['source_hashes'].items():
        assert digest(Path(__file__).with_name(name))==value
    tests=json.loads((OUT/'tests.json').read_text())
    for name,value in host['source_hashes'].items():
        assert tests['hashes']['tools/resource-slab-20261024/'+name]==value['sha256']
    # Earlier evidence and original tools must remain untouched, including all
    # historical failures; existing files cannot be repaired retroactively.
    changed=subprocess.check_output(['git','diff','--name-only','c7a02ff113','--','evidence/resource-slab-20261024','tools/resource-slab-20261024'],cwd=ROOT,text=True).splitlines()
    old=set(subprocess.check_output(['git','ls-tree','-r','--name-only','c7a02ff113','--','evidence/resource-slab-20261024','tools/resource-slab-20261024'],cwd=ROOT,text=True).splitlines())
    assert not old.intersection(changed)
    assert not subprocess.check_output(['git','diff','c7a02ff113','--','crates','programs'],cwd=ROOT)
    paths=sorted(p for p in OUT.iterdir() if p.is_file() and p.name not in ('artifact-hashes.json','finalize-receipt.json'))
    assert all(p.stat().st_size<=5_000_000 for p in paths if p.suffix=='.json')
    assert all(p.suffix in ('.json','.txt','.log','.md','.stdout','.time') for p in paths)
    manifest={str(p.relative_to(ROOT)):digest(p) for p in paths}
    for p in sorted(Path(__file__).parent.glob('*.py')):manifest[str(p.relative_to(ROOT))]=digest(p)
    (OUT/'artifact-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
    usage=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(command=['python3','-B','tools/resource-slab-20261024/finalize_go.py'],exit=0,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swaps=usage.ru_nswap,
        platform='macOS self; child/aggregate N/A',source_dependency_input_manifest=digest(OUT/'artifact-hashes.json'),
        source=digest(Path(__file__)),legacy_and_earlier_evidence_unchanged=True,
        host_source_matches_current=True,tested_operational_sources_match_current=True,
        print_axioms='N/A; formal budget ZERO')
    (OUT/'finalize-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
if __name__=='__main__':main()
