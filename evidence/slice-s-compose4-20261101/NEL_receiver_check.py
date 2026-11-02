"""Type-resolution check only; no iterator/order/frame result is inferred."""
import subprocess,hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
PATHS=['crates/aspis-statement/src/atomic_statement.rs','crates/aspis-statement/src/poseidon2.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/transcript.rs']
def frozen():return {p:subprocess.check_output(['git','show',REV+':'+p],cwd=R,text=True) for p in PATHS}
def check(s):
 a,p,f,t=(s[n] for n in PATHS)
 return ('field::{M31, P}' in a and 'poseidon2::{hash_merkle_node_sponge, Digest, DIGEST_ELEMS}' in a and 'pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32]' in a and 'for (index, value) in digest.iter().enumerate()' in a and 'value.to_le_bytes()' in a and 'use aspis_core::field::M31;' in p and 'pub type Digest = [M31; DIGEST_ELEMS];' in p and 'pub const DIGEST_ELEMS: usize = 8;' in p and 'pub fn to_le_bytes(self) -> [u8; 4] {\n        self.0.to_le_bytes()\n    }' in f and 'fn to_le_bytes' not in t)
if __name__=='__main__':
 import copy
 s=frozen();assert check(s);tests=1
 for path,old,new in [(PATHS[1],'pub type Digest = [M31;','pub type Digest = [WideExact;'),(PATHS[2],'pub fn to_le_bytes(self) -> [u8; 4]','pub fn to_le_bytes(self) -> [u8; 32]'),(PATHS[3],'pub trait HashFn','pub trait HashFn')]:
  mutant=copy.deepcopy(s)
  if path==PATHS[3]:mutant[path]+='\nfn to_le_bytes() {}\n'
  else:assert old in mutant[path];mutant[path]=mutant[path].replace(old,new)
  assert not check(mutant);tests+=1
 (E/'NEL_RECEIVER.json').write_text(json.dumps(dict(frozen_revision=REV,source_sha256={p:hashlib.sha256(v.encode()).hexdigest() for p,v in s.items()},checks=tests,receiver='&M31',excluded='WideExact',scope='static call resolution only; actual Enumerate state/count transport remains OPEN'),indent=1)+'\n')
