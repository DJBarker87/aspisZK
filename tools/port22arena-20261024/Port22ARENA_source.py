#!/usr/bin/env python3
"""Targeted immutable source assessment, not a new release identity gate."""
import hashlib,json,pathlib,subprocess,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/port22arena-20261024'
sha=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic();old=R/'evidence/port21projection-20261024'
rows=[]
# Only dependencies used by this primitive and its immediate helper route.
for name in ['crates/aspis-core/src/r0/heap.rs','crates/aspis-core/src/field.rs','crates/aspis-r1-cost-probe/src/verifier.rs']:
 item=next(x for x in json.loads((old/'source-pins.json').read_text())['source_inclusions'] if x['source']==name)
 b=(R/name).read_bytes();assert sha(b)==item['whole_sha256']
 rows.append(dict(path=name,sha256=sha(b),bytes=len(b),assessment='Current worktree bytes equal historical exact-source pin; no new ELF identity claim'))
rt=json.loads((old/'runtime-source-graph.json').read_text())
for item in rt['files']:
 if item['path'].endswith('programs/r1-cost-probe/src/lib.rs'):
  b=(R/item['path']).read_bytes();assert sha(b)==item['sha256'];rows.append(dict(path=item['path'],sha256=sha(b),bytes=len(b)))
selected=R/'tools/port22arena-20261024/Port22ARENA-native/src/Port22ARENA_selected.rs'
p=pathlib.Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-program-entrypoint-2.3.0/src/lib.rs')
item=next(x for x in rt['files'] if x['path']==str(p));assert sha(p.read_bytes())==item['sha256']
assert selected.read_text().rstrip() in p.read_text()
rows.append(dict(path=str(p),sha256=sha(p.read_bytes()),selected_sha256=sha(selected.read_bytes()),exact_contiguous_source=True))
code="""from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
rows=[]
for rel,spans in [('core/src/clone.rs',[(684,721)]),('alloc/src/alloc.rs',[(201,218)]),('core/src/array/mod.rs',[(443,488)]),('alloc/src/vec/mod.rs',[(1580,1582),(3529,3537),(3655,3681)]),('alloc/src/raw_vec/mod.rs',[(719,736),(772,805),(543,567)])]:
 p=root/rel;b=p.read_bytes();ls=b.decode().splitlines()
 rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),spans=[dict(start_line=a,end_line=z,text='\\n'.join(ls[a-1:z])) for a,z in spans]))
print(json.dumps(rows,indent=2))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
std=json.loads(r.stdout);prior=json.loads((old/'std-source-graph-complete.json').read_text())['files']
for row in std:
 match=next((x for x in prior if x['path']==row['path']),None)
 if match:assert match['sha256']==row['sha256']
 row['historical_pin_matched']=bool(match)
result=dict(schema='Port22ARENA-source-assessment-v1',command='python3 tools/port22arena-20261024/Port22ARENA_source.py',script_sha256=sha(pathlib.Path(__file__).read_bytes()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),exit_status=0,wall_seconds=time.monotonic()-start,source_dependencies=rows,host_std=std,remote_read_command=['ssh','dombarker@100.108.41.90','python3','-'],remote_read_script=code,print_axioms='N/A: read-only source assessment',assessment='Host extraction std differs from Kani sysroot and SBF sysroot. Exact copied allocator body checked with Kani; shim/Vec/deployed associations not proved.')
(E/'source-assessment.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(exit_status=0,matched_source_dependencies=len(rows),std_files=len(std))))
