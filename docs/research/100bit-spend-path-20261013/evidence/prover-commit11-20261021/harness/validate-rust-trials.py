#!/usr/bin/env python3
"""Check excluded candidate source identities and capped trial receipts."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
ROOT=E.parents[4]
assert not subprocess.check_output(['git','diff','--name-only','8e4931b1f','--','crates','programs','Cargo.toml','Cargo.lock','.cargo'],cwd=ROOT,text=True).strip()
catalog={}
for p in (E/'rust-drafts').glob('*/*.txt'):
    catalog.setdefault('crates/aspis-prover/src/'+p.name[:-4],set()).add(hashlib.sha256(p.read_bytes()).hexdigest())
rows=[]
for d in sorted((E/'receipts').iterdir()):
    r=json.loads((d/'receipt.json').read_text())
    inputs=json.loads((E/(d.name+'-inputs.json')).read_text())
    for rel,sha in inputs['source_hashes'].items():
        assert not Path(rel).is_absolute() and '..' not in Path(rel).parts
        p=ROOT/rel
        possible=catalog.get(rel,set())|({hashlib.sha256(p.read_bytes()).hexdigest()} if p.exists() else set())
        assert sha in possible,(d.name,rel,sha)
    assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
    assert r['swaps']==0
    assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
    assert r['env']['CARGO_BUILD_JOBS']=='4'
    assert '--unwinding-assertions' in r['command']
    rows.append(dict(name=d.name,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],swaps=r['swaps'],full_contract_certified=False))
meta=json.loads((E/'scalar-offset-0-v8.json').read_text())
h=meta['proof_harnesses'][0]
assert h['attributes']['kind']['ProofForContract']['target_fn']=='SeedExpander::m31'
assert set(h['attributes']['verified_stubs'])=={'state_only_hiding::SeedExpander::next_word','prover_commit_reference::next','prover_commit_oracle::expander_query'}
print(json.dumps(dict(trials=rows,adopted_rust_unchanged=True,new_full_contract_certified=False),indent=1))
