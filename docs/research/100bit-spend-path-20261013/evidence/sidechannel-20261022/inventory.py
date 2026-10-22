#!/usr/bin/env python3
"""Reproducible lexical source-review index, NOT static reachability analysis."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[4]
files={}
def add(path,family):
    files[path]=family
for f in ['prover','host_semantic','host_sumcheck','host_commitment','sampler','transcript','r1_wire','weights','transport','multiproof','compact','trace','sim']:
    add('crates/aspis-r1-cost-probe/src/'+f+'.rs','report selected route table: '+f)
for f in ['state_only_entropy','state_only_hiding']:
    add('crates/aspis-prover/src/'+f+'.rs','report preparation table: '+f)
for f in ['field','field/wide_exact','circle','r0_transcript','state_only_hiding','state_only_sumcheck','state_only_private_merkle','digest','r0/mod','r0/domain','r0/encoder','r0/basis','r0/fold','r0/heap']:
    add('crates/aspis-core/src/'+f+'.rs','report F2 / fixed geometry / transcript table: '+f)
for f in ['logup','constraints_v4','state_only_poseidon','poseidon2','pool_v1/pair_forest_semantic_oracle','pool_v1/pair_forest_semantic_terminal','pool_v1/pair_forest_copy_terminal','pool_v1/pair_forest_trace','pool_v1/pair_forest_hiding','pool_v1/pair_forest_copy_builder','pool_v1/pair_trace']:
    add('crates/aspis-statement/src/'+f+'.rs','report semantic tables / F2 F4 F5: '+f)
for f in ['probe','z5','z9','z9b','z9c','z9d','z9e','r1p_lib']:
    add('docs/research/v8-r0-zk-20261009/z4/'+f+'.rs','report checker table / F1 F2 F5 F6: '+f)
for f in ['build','check']:
    add('docs/research/v8-r0-zk-20261009/c3/'+f+'/src/lib.rs','report c3 '+f+' row / F2 F6')
for f in ['tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/v7-live-pool-proof/src/lib.rs','scripts/r1_devnet_spend.py','scripts/r1_devnet_rpc.py']:
    add(f,'report F8 caller boundary; not substituted for requested route')
manifest=[]
for rel,family in files.items():
    p=R/rel;raw=p.read_bytes();lines=raw.decode().splitlines()
    declarations=[];sites=[]
    for n,l in enumerate(lines,1):
        m=re.search(r'\bfn\s+([A-Za-z_]\w*)|^def\s+(\w+)',l)
        if m:
            declarations.append(dict(line=n,name=m.group(1) or m.group(2),classification_family=family,declaration=l.strip(),scope='lexical candidate: may be fixture, test, cfg-only, CLI, verifier or unreachable shared helper; selected functions identified in report'))
        if l.lstrip().startswith(('//','# ')): continue
        kinds=[]
        for kind,pat in [
            ('branch/early-exit',r'\b(if|match|return|break|continue)\b|\?|&&|\|\|'),
            ('loop/iterator',r'\b(for|while|loop)\b|\.(any|all|position|find|contains|take_while)\('),
            ('allocation/collection',r'BTree|Vec::|vec!|\.((try_)?reserve(_exact)?|push|insert|entry|get|sort(_unstable)?|dedup|resize)\('),
            ('arithmetic/decoding',r'\.(try_inv|inv|pow|from_le_bytes)\(|\bfrom_le_bytes| / | % '),
            ('I/O/timing',r'write_all|sync_all|create_new|Instant::|elapsed\(|fs::write|rpc\(')]:
            if re.search(pat,l):kinds.append(kind)
        if kinds:sites.append(dict(line=n,kinds=kinds,source=l.strip()))
    manifest.append(dict(path=rel,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),classification_family=family,declarations=declarations,operation_sites=sites))
# Pin feature/toolchain boundary inputs as well, without interpreting their targets.
pins=[]
for rel in ['Cargo.lock','Cargo.toml','rust-toolchain.toml','crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-prover/Cargo.toml','docs/research/v8-r0-zk-20261009/z4/Cargo.toml','docs/research/v8-r0-zk-20261009/z4/Cargo.lock','tools/r1-cost-probe/Cargo.toml','programs/r1-cost-probe/Cargo.toml']:
    p=R/rel
    if p.exists():
        b=p.read_bytes();pins.append(dict(path=rel,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
out=dict(source_baseline='89013d67f06f2b8bf1ab53339d107e60a7cca556',inventory_at_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),method='lexical superset, no Rust parser, cfg resolution, macro expansion or static call graph; semantic classifications are the report tables, not inferred by regex',files=manifest,configuration_pins=pins,summary=dict(files=len(manifest),declarations=sum(len(x['declarations']) for x in manifest),operation_sites=sum(len(x['operation_sites']) for x in manifest)))
(E/'source-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out['summary']))
