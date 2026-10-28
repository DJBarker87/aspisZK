"""Textual source inventory only; not a taint proof or a native equivalence."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
groups={
'V356':['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/host_sampler.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-core/src/circle.rs','crates/aspis-core/src/r0_transcript.rs'],
'V358':['crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/transcript.rs','crates/aspis-r1-cost-probe/src/host_transcript.rs'],
'V361':['docs/research/v8-r0-zk-20261009/z4/z9c.rs','docs/research/v8-r0-zk-20261009/z4/z9d.rs','docs/research/v8-r0-zk-20261009/z4/z9e.rs'],
'V362':['docs/research/v8-r0-zk-20261009/z4/z9.rs','docs/research/v8-r0-zk-20261009/z4/z9b.rs','docs/research/v8-r0-zk-20261009/z4/probe.rs'],
'V363':['docs/research/v8-r0-zk-20261009/c3/build/src/lib.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_m31.rs','docs/research/v8-r0-zk-20261009/c3/build/Cargo.toml'],
'V364':['docs/research/v8-r0-zk-20261009/c3/check/src/lib.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','docs/research/v8-r0-zk-20261009/c3/check/Cargo.toml'],
'V365':['crates/aspis-r1-cost-probe/src/sim.rs']}
rows=[]
for row,paths in groups.items():
 for path in paths:
  p=R/path;b=p.read_bytes();ls=b.decode().splitlines()
  rows.append(dict(row=row,path=path,source_sha256=hashlib.sha256(b).hexdigest(),
   declarations=[dict(line=i+1,text=l.strip()) for i,l in enumerate(ls) if re.search(r'\bfn\s+|\bstatic\s+|thread_local!',l)],
   controls=[dict(line=i+1,text=l.strip()) for i,l in enumerate(ls) if re.search(r'\b(if|else|while|for|match|continue|break|return|assert|debug_assert)\b|#\[cfg|\.get\(|\.get_mut\(|\.sort|\.dedup|\.insert\(|\.binary_search',l)]))
v=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),class_='source inspection / textual inventory ONLY',rows=rows,features='deployed-client-features.json',excluded_credit='No complete Result law/native differential for V361-V365; no source-to-simE theorem or row removal')
(E/'remaining-site-inventory.json').write_text(json.dumps(v,indent=2)+'\n')
print(len(rows),'file/site entries inventoried')
