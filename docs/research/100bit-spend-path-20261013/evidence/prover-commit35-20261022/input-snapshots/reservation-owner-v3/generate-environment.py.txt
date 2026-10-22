#!/usr/bin/env python3
"""Pin verbatim native callees; only primitive/type substitutes live in lib.rs."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
source=Path('crates/aspis-prover/src/state_only_entropy.rs').read_text()
def extract(needle):
 start=source.index(needle);left=source.index('{',start);i=left+1;depth=1
 while depth:depth+=(source[i]=='{')-(source[i]=='}');i+=1
 return source[start:i]
parts={
 'native-generate.rs':'impl StateOnlyAttemptSecrets {\n'+extract('pub fn generate()')+'\n}\n',
 'native-reserve.rs':'impl DurableStateOnlyMaskNonceStore {\n'+extract('pub fn reserve_fallible(')+'\n}\nimpl StateOnlyMaskNonceStore for DurableStateOnlyMaskNonceStore {\n'+extract('fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {\n        match self.reserve_fallible')+'\n}\n',
 'native-build.rs':'impl StateOnlyAttemptSecrets {\n'+extract('pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(')+'\n}\n',
}
for name,body in parts.items():(H/name).write_text(body)
(H.parent/'environment-source-pins.json').write_text(json.dumps(dict(source_path='crates/aspis-prover/src/state_only_entropy.rs',source_sha256=hashlib.sha256(source.encode()).hexdigest(),verbatim_functions={name:hashlib.sha256(body.encode()).hexdigest() for name,body in parts.items()},substitutes='OS primitives, zeroizing storage, public path computation, downstream mask builder and hash. No native std internals or field arithmetic certified.'),indent=2)+'\n')
