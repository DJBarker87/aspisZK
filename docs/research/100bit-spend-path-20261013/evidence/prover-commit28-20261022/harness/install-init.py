"""Host-only named extraction root calling the unchanged native initializer."""
from pathlib import Path
import hashlib,json
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit28-20261022')
p=R/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs'
s=p.read_text();assert 'pub mod init28' not in s
addition='''
#[cfg(aeneas_ref)]
pub mod init28 {
    use super::*;
    pub fn make<H: Digest32>(hash: H, public_bytes: &[u8], c1_root: &[u8; 32])
        -> Result<SemanticTranscript<H>, Error> {
        SemanticTranscript::new(hash, public_bytes, c1_root)
    }
}
'''
(R/'init-wrapper.json').write_text(json.dumps(dict(native_sha256=hashlib.sha256(s.encode()).hexdigest(),addition=addition),indent=2)+'\n')
p.write_text(s+addition)
