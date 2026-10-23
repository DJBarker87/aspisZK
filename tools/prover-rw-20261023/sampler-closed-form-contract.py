#!/usr/bin/env python3
"""Check one exact long-division word step, not the full sampler loop."""
from pathlib import Path
import hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[2];C=R/'tools/prover-rw-20261023/contracts'
p=R/'crates/aspis-r1-cost-probe/src/sampler.rs';text=p.read_text()
a=text.index('        let dividend = (remainder << 32) | u64::from(rank[j]);');last='        remainder = dividend % u64::from(P);';b=text.index(last,a)+len(last);fragment=text[a:b]
(C/'sampler_word_source.rs').write_text('use aspis_core::field::P;\npub fn actual(word:u32,mut remainder:u64)->(u32,u64) {\n let mut rank=[word];let j=0;\n'+fragment+'\n (rank[0],remainder)\n}\n')
(C/'sampler-word-bindings.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),fragment_sha256=hashlib.sha256(fragment.encode()).hexdigest(),adaptation='Verbatim three-statement loop body, with rank=[word] and j=0; index selection/control is a separate obligation',domain='All u32 words; prior remainder in 0..P. Exact quotient word, canonical remainder and division identity. Not the whole 8-word pass or a sampler distribution law.'),indent=2)+'\n')
cmd=['timeout','120','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','sampler_word_contracts::word_closed_form_arithmetic','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'sampler-closed-form-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compile then Mersenne quotient/remainder arithmetic, bounded quotient and remainder plus shift reconstruction; native division equality remains open, arbitrary u32 word and canonical prior remainder; no full sampler-loop bit-blast'),check=True)
