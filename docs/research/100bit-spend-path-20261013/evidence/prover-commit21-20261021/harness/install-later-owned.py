from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/transcript.rs';original=p.read_text()
assert 'mod owned21' not in original
body=original[original.index('pub struct Transcript'):]
body=body[:body.index('#[cfg(kani)]')] if '#[cfg(kani)]' in body else body
body=body.replace('pub state:[u8;32], hash:H','pub state:[u8;32], hash:H, pub trace:alloc::vec::Vec<(u16,usize,[u8;32])>')
body=body.replace('semantic_state]), hash }','semantic_state]), hash, trace:alloc::vec::Vec::new() }')
body=body.replace('crate::trace::value(4,row as usize,out)', 'self.trace.push((4,row as usize,out.to_le_bytes()))')
body=body.replace('crate::trace::value(4,row as usize,E::from_qm31(out))','self.trace.push((4,row as usize,E::from_qm31(out).to_le_bytes()))')
import re
body,n=re.subn(r'crate::trace::value\(5,(\d+),E::from_m31\(aspis_core::field::M31\(u\)\)\)',r'self.trace.push((5,\1,E::from_m31(aspis_core::field::M31(u)).to_le_bytes()))',body)
assert n==22 and 'crate::trace' not in body
addition='\n#[cfg(any(kani,aeneas_ref))]\npub mod owned21 {\nuse super::*;\n'+body+'\n}\n'
p.unlink();p.write_text(original+addition)
(H/'harness/transcript-owned21.rs').write_text(addition)
(H/'transcript21-binding.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),addition_sha256=hashlib.sha256(addition.encode()).hexdigest(),edits=['Return native TLS value records through an owned Vec','Retain every scalar and query trace value in the same order','No hash/sampler/query routine replaced'],boundary='TLS-to-owned Vec identification remains open'),indent=2)+'\n')
