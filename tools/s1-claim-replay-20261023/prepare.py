#!/usr/bin/env python3
"""Replay every reached leaf's complete numeric inputs and output.
This is a source-control coupling certificate, not actual leaf installation.
"""
from pathlib import Path
import hashlib, json, subprocess, sys
R=Path(__file__).resolve().parents[2]
O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s1-claim-fission-point-20261023/prepare.py'),str(O)],check=True)
ghost='\n#[cfg(kani)] impl<H: Digest32> SemanticTranscript<H> { pub fn proof_input(hash:H,state:[u8;32],next_row:u8)->Self { Self{state,hash,next_row} } }\n'
wire=O/'frozen-probe/src/r1_wire.rs'
wire.write_text(wire.read_text()+ghost)
proof='accepted.rs' if '--accepted' in sys.argv[2:] else 'proofs.rs'
(O/'src/proofs.rs').write_bytes((Path(__file__).parent/proof).read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'replay-binding.json').write_text(json.dumps(dict(
    schema='focused-extractor-proof-packet-v1', qualification=__doc__,
    proof_sha256=sha(O/'src/proofs.rs'), source_sha256=sha(O/'src/lib.rs'),
    ghost_constructor=ghost,
    leaf_port='push: all9 state u64 words +8 value u32 words +4 scalar u32 words, all9 output state words; finish: all9 state words; field: same exact slice pointer/length and ordered index',
    rejection_schedule=('29 successful pushes only; accepted-only experiment' if proof=='accepted.rs' else 'stop in0..=29: first Err at stop<29, or29 successful pushes; every possible first rejection is represented'),
    remaining='Actual leaf interpretation and source/P6/caller transport; field aborts outside the fixed admitted928-byte input are not represented.'),indent=2)+'\n')
