#!/usr/bin/env python3
"""Pure leaf-function overapproximation, on complete actual numeric carriers.
C UF arguments include every input bit; no tables, hashes or reduced state.
Original source algorithms are not adopted/edited in production.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);subprocess.run(['python3',str(R/'tools/s1-claim-fission-point-20261023/prepare.py'),str(O)],check=True)
wire=O/'frozen-probe/src/r1_wire.rs'
ghost='\n#[cfg(kani)] impl<H: Digest32> SemanticTranscript<H> { pub fn proof_input(hash:H,state:[u8;32],next_row:u8)->Self { Self{state,hash,next_row} } }\n'
wire.write_text(wire.read_text()+ghost)
(O/'src/proofs.rs').write_bytes((Path(__file__).parent/'proofs.rs').read_bytes())
c=['#include <stdint.h>','']
for name,intype,incount,outtype,outcount in [('raw','uint32_t',8,'uint64_t',4),('finish','uint64_t',9,'uint32_t',8),('field','uint32_t',8,'uint32_t',8),('mul','uint32_t',16,'uint32_t',8),('add','uint32_t',16,'uint32_t',8),('push','uint64_t',21,'uint64_t',10)]:
 args=','.join(f'{intype} x{i}' for i in range(incount));actual=','.join(f'input[{i}]' for i in range(incount))
 for j in range(outcount):c.append(f'extern {outtype} __CPROVER_uninterpreted_aspis_{name}_{j}({args});')
 c.append(f'uint32_t aspis_uf_{name}(const {intype} *input,{outtype} *output) {{')
 for j in range(outcount):c.append(f' output[{j}]=__CPROVER_uninterpreted_aspis_{name}_{j}({actual});')
 c+=[' return 0;','}','']
(O/'leaves.c').write_text('\n'.join(c)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'uf-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification=__doc__,leaf_input_fields=dict(raw='all eight u32 coordinates of Q,Q',finish='all nine u64 words of complete EbyKDot',field='all eight u32 little-endian words of the exact32-byte field frame',mul='all sixteen u32 words of two complete WideExact values',add='all sixteen u32 words of two complete WideExact values'),source_sha256=sha(O/'src/lib.rs'),pairing_sha256=sha(O/'src/fast_pairing.rs'),proof_sha256=sha(O/'src/proofs.rs'),c_sha256=sha(O/'leaves.c'),primary_reference='https://github.com/diffblue/cbmc/blob/8fcda333650440a60d3a054552a7ad318255b95d/regression/cbmc/uninterpreted_function/uf2.c',proof_only_input_constructor=ghost,push_port='all nine full state u64 words, eight value u32 words and four scalar u32 words, zero-extended injectively; nine state words and a one-bit result',remaining='Pure actual-leaf instantiation, source/P6 and release binding; parser aborts not represented by the total field port. No whole-source closure is presumed.'),indent=2)+'\n')
