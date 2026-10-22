#!/usr/bin/env python3
"""Read-only production section and resource/source evidence audit."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-bytes2-20261022'
verifier=(R/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
reader=verifier[verifier.index("struct Reader<'a>"):verifier.index('\n\n\n#[inline(always)]\nfn validate_checkpoint_queries')]
assert (R/'tools/ckpt-bytes2-20261022/src/reader-source.rs').read_text()==reader+'\n'
checks={'reader_k_16':'K::from_le_bytes(&self.raw::<16>())' in reader,
        'reader_e_32':'E::from_le_bytes(&self.raw::<32>())' in reader,
        'raw_exact_cursor':'self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N' in reader,
        'total_width_guard':'bytes.len()!=checkpoint_size(v)' in verifier,
        'final_cursor_guard':'if at!=end {return Err(Error::Checkpoint);}' in verifier,
        'fallible_allocation':'heap::filled(v.final_len(),K::ZERO).map_err(|_|Error::Allocation)?' in verifier}
assert all(checks.values())
pins={str(p.relative_to(R)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
      for p in [R/'crates/aspis-r1-cost-probe/src/verifier.rs',R/'crates/aspis-core/src/field.rs',R/'crates/aspis-core/src/field/wide_exact.rs',R/'tools/ckpt-bytes2-20261022/src/reader-source.rs']}
rec=json.loads((E/'kani/k-section-current-1/receipt.json').read_text())
mismatch=[name for name,sha in rec['source_sha256'].items() if (R/name).exists() and hashlib.sha256((R/name).read_bytes()).hexdigest()!=sha]
assert not mismatch,mismatch
assert rec['exit_status']==0
assert 'VERIFICATION SUCCESSFUL' in (E/'kani/k-section-current-1/stdout.log').read_text()
(E/'source-check.json').write_text(json.dumps({'checks':checks,'source_pins':pins,'host_receipt':'kani/k-section-current-1/receipt.json','host_pins_compared':len(rec['source_sha256']),'host_mismatches':mismatch,'scope':'source-body identity plus production section Kani; no whole-function harness or kernel Rust adoption inferred'},indent=2)+'\n')
print(json.dumps(checks))
