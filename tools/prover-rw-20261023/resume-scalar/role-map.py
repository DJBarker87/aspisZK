"""Bind roles to concrete source statements, never event payload uniqueness."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
s=(D/'proof/selected.rs').read_text()
anchors={
 'draw-live64':'let mut bytes = Zeroizing::new([0u8; 64]);',
 'draw-call':'let outcome = getrandom::fill(bytes.as_mut());',
 'draw-move':'ProverRwResumeScalarDraw { request: self, bytes, outcome }',
 'resume-move':'let Self { mut request, bytes, outcome } = self;',
 'error-return':'Err(StateOnlyAttemptEntropyError::from(error)),',
 'field-local':'let mut field_mask_entropy = Zeroizing::new([0u8; 32]);',
 'leaf-local':'let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);',
 'field-copy':'field_mask_entropy.copy_from_slice(&bytes[..32]);',
 'leaf-copy':'leaf_salt_seed.copy_from_slice(&bytes[32..]);',
 'accepted-move':'Ok(Some(StateOnlyAttemptSecrets {\n                    mask_nonce: request.mask_nonce,\n                    field_mask_entropy,\n                    leaf_salt_seed,\n                }))',
 'retry-before-drop':'request.retry += 1;',
 'return-more':'(ProverRwResumeScalarControl::More(request), Ok(None))',
 'field-declaration':'field_mask_entropy: Zeroizing<[u8; 32]>,',
 'leaf-declaration':'leaf_salt_seed: Zeroizing<[u8; 32]>,',
}
rows={}
for role,text in anchors.items():
 assert s.count(text)==1,(role,s.count(text));a=s.index(text)
 rows[role]=dict(byte_start=a,byte_end=a+len(text),line=s[:a].count('\n')+1,text=text,sha256=hashlib.sha256(text.encode()).hexdigest())
assert rows['retry-before-drop']['byte_start']>rows['accepted-move']['byte_start']
out=dict(schema='ProverRwResumeScalar-role-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),bindings=rows,normal_paths={'Err':['bytes64'],'Ok-accept-resume':['bytes64'],'Ok-accept-later-disposal':['Secrets.field32','Secrets.leaf32'],'Ok-reject':['leaf-local32','field-local32','bytes64']},identification='source places, aggregate field moves and drop flags, never equal bytes or invocation ordinals',MIR_status='separate optimized compile evidence; not an extraction or native refinement theorem')
(D/'source-role-map.json').write_text(json.dumps(out,indent=2)+'\n')
