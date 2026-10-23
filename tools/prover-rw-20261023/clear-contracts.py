#!/usr/bin/env python3
"""Copy exact tiny volatile leaf bodies and verify their selected-cell frames."""
from pathlib import Path
import hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[2];C=R/'tools/prover-rw-20261023/contracts'
rows=[];parts=[]
for file,name in [('crates/aspis-r1-cost-probe/src/host_commitment.rs','clear_private_salt'),('crates/aspis-prover/src/state_only_hiding.rs','volatile_clear_cell')]:
 s=(R/file).read_text();a=s.index('pub(crate) fn '+name);b=s.index('{',a);depth=1;end=b+1
 while depth:
  depth+=(s[end]=='{')-(s[end]=='}');end+=1
 body=s[a:end];parts.append(body)
 rows.append(dict(source=file,function=name,verbatim_sha256=hashlib.sha256(body.encode()).hexdigest(),source_sha256=hashlib.sha256((R/file).read_bytes()).hexdigest()))
(C/'clear_source.rs').write_text('\n\n'.join(parts)+'\n')
(C/'clear-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for name in ['salt_cell_frame','m31_cell_frame','qm31_cell_frame']:
 cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','clear_contracts::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'clear-kani-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then exact single-cell volatile overwrite/frame, arbitrary raw input bits, selected index among three cells; no whole-vector or zeroization-order conclusion'),check=True)
