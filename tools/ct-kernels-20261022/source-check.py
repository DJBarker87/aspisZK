#!/usr/bin/env python3
"""Local, read-only byte/line preservation and instrumentation provenance checks."""
from pathlib import Path
import subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];base='87545bd40543d6189f3aff8be6d3391759ea2dd7';rows=[]
for path in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs']:
 old=subprocess.check_output(['git','show',base+':'+path],cwd=R).decode()
 new=(R/path).read_text();prefix='\n'.join(new.splitlines()[:len(old.splitlines())])+'\n'
 recovered=prefix.replace('#[cfg(not(feature = "ct-host-prover"))] ','')
 assert recovered==old,path
 rows.append(dict(path=path,baseline_sha256=hashlib.sha256(old.encode()).hexdigest(),candidate_sha256=hashlib.sha256(new.encode()).hexdigest(),original_body_and_line_preserved=True))
old=subprocess.check_output(['git','show',base+':crates/aspis-core/src/field.rs'],cwd=R).decode()
assert (R/'tools/ct-kernels-20261022/reference/field.rs').read_text().replace('#[path = "field/wide_exact.rs"] mod wide_exact;','mod wide_exact;')==old
assert (R/'tools/ct-kernels-20261022/reference/field/wide_exact.rs').read_bytes()==subprocess.check_output(['git','show',base+':crates/aspis-core/src/field/wide_exact.rs'],cwd=R)
p=R/'tools/ct-kernels-20261022/instrumented.rs';before=p.read_bytes()
provenance=json.loads(subprocess.check_output(['python3',str(R/'tools/ct-kernels-20261022/instrument.py')],cwd=R))
assert p.read_bytes()==before,'stale generated instrumentation'
for path in ['programs/r1-cost-probe','programs/aspis-pool','crates/aspis-statement']:
 assert subprocess.check_output(['git','diff',base,'--',path],cwd=R)==b'',path
print(json.dumps(dict(baseline_revision=base,field_sources=rows,instrumentation=provenance,program_and_statement_sources_unchanged=True,classification='Source checks; not Kani, ELF identity, or L3 proof'),indent=2))
