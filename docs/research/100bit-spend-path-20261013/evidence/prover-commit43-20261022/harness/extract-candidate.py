from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
source=Path('crates/aspis-core/src/state_only_entropy.rs')
if not source.exists():
 source=next(Path('crates').rglob('state_only_entropy.rs'))
s=source.read_text()
start=s.index('            let mut bytes = Zeroizing::new([0u8; 64]);',s.index('pub fn generate_for_mask_nonce('))
end=s.index('\n        }\n        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)',start)
body=s[start:end]
# Only return wrapping changes: native success exits the loop; owner transition
# returns Some on terminal outcomes and None on the native fall-through edge.
body=body.replace('getrandom::fill(bytes.as_mut())?;', 'match getrandom::fill(bytes.as_mut()) {Ok(())=>(),Err(e)=>return Some(Err(e.into()))};')
body=body.replace('return Ok(Self {','return Some(Ok(Self {').replace('                });','                }));')
out='impl StateOnlyAttemptSecrets {\nfn candidate(mask_nonce:[u8;32])->Option<Result<Self,StateOnlyAttemptEntropyError>> {\n'+body+'\n None\n}\n}\n'
(H/'native-candidate.rs').write_text(out)
(H/'native-source-check.json').write_text(json.dumps(dict(source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),original_body=s[start:end],candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),transformations=['wrap native success in Some','OS ? becomes Some(Err(Os))','fall-through becomes None'],loop_range='0..ENTROPY_RETRY_LIMIT; ENTROPY_RETRY_LIMIT = 16'),indent=2)+'\n')
