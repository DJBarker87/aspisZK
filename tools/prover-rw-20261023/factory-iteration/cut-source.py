"""Generate one-draw candidate from exact loop body; NOT semantic equivalence."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
original=(D.parent/'factory-cleanup/proof/selected.rs').read_text()
a=original.index('impl StateOnlyAttemptSecrets {')
header=original[:a]
b=original.index('        while retry<limit {')
start=b+len('        while retry<limit {')
depth=1;end=start
while depth:
 if original[end]=='{':depth+=1
 if original[end]=='}':depth-=1
 end+=1
body=original[start:end-1]
old='return Ok(Self {\n                    mask_nonce,\n                    field_mask_entropy,\n                    leaf_salt_seed,\n                });'
new='return Ok((retry, Some(Self {\n                    mask_nonce,\n                    field_mask_entropy,\n                    leaf_salt_seed,\n                })));'
assert body.count(old)==1
changed=body.replace(old,new)
text=header+'''impl StateOnlyAttemptSecrets {
    // CANDIDATE CUT: one admitted iteration, not generate_for_mask_nonce.
    pub fn one_draw(
        mask_nonce: [u8;32], mut retry: usize,
    ) -> Result<(usize, Option<Self>), StateOnlyAttemptEntropyError> {
        {'''+changed+'''}
        Ok((retry, None))
    }
}
'''
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
meta=dict(schema='ProverRwFactoryIteration-cut-source-v1',original_selected_sha256=sha(original),original_loop_body=dict(start_byte=start,end_byte=end-1,start_line=original[:start].count('\n')+1,end_line=original[:end-1].count('\n')+1,sha256=sha(body)),cut_sha256=sha(text),success_before=old,success_after=new,body_changes='Only success return container; all other loop-body bytes including retry+=1 and lexical end scope identical.',outer_changes=['Remove nonce guard and retry loop: entry represents admitted iteration','Initialize local retry from argument','Return (retry,None) after rejection scope; not actual factory exhaustion'],scope='Checked syntactic factoring only. Mechanized equivalence to actual body/caller/MIR and finite16 composition OPEN. Actual Zeroizing/Drop kept; no event instrumentation.')
for p,data in [(D/'proof-cut/selected.rs',text),(D/'cut-source-map.json',json.dumps(meta,indent=2)+'\n')]:
 if '--check' in sys.argv:assert p.read_text()==data,p
 else:p.write_text(data)
print('one-draw cut fragments checked; semantic caller association OPEN')
