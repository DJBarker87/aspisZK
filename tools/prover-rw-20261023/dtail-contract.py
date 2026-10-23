#!/usr/bin/env python3
"""Exact D-tail recurrence against the literal v2 fragment, canonical QM31."""
from pathlib import Path
import hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[2];C=R/'tools/prover-rw-20261023/contracts'
p=R/'crates/aspis-r1-cost-probe/src/host_semantic.rs';s=p.read_text();parts=[];pins=[]
for name in ['add_d_tail','d_tail_side','d_tail_sum']:
 a=s.index('fn '+name+'(');b=s.index('{',a);depth=1;end=b+1
 while depth:
  depth+=(s[end]=='{')-(s[end]=='}');end+=1
 body=s[a:end];parts.append(body);pins.append(dict(function=name,sha256=hashlib.sha256(body.encode()).hexdigest()))
old=subprocess.check_output(['git','show','084f714ccd:crates/aspis-r1-cost-probe/src/host_semantic.rs'],cwd=R,text=True) if (R/'.git').exists() else (C/'dtail-v2.rs.txt').read_text()
a=old.index('        for side in 0..2 {');b=old.index('        let eta =',a);fragment=old[a:b]
(C/'dtail_source.rs').write_text('use aspis_core::field::{QM31,M31};\n'+'\n\n'.join(parts)+'''\npub(crate) fn actual(mask_sum:QM31,dc:&[QM31;1024])->QM31 {add_d_tail(mask_sum,dc)}
pub(crate) fn expected(mut mask_sum:QM31,dc:&[QM31;1024])->QM31 {
'''+fragment+'mask_sum\n}\n')
(C/'dtail-bindings.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),functions=pins,reference_revision='084f714ccd',reference_fragment_sha256=hashlib.sha256(fragment.encode()).hexdigest()),indent=2)+'\n')
cmd=['timeout','120','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','dtail_contracts::exact_d_tail','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'dtail-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then exact 28-term source recurrence versus literal v2 D-tail fragment; arbitrary canonical first 56 QM31 coefficients and initial claim'),check=True)
