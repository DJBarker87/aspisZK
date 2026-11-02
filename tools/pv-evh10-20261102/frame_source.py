"""Source statement inventory for the original entropy frame; not native adequacy."""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path('evidence/pv-evh10-20261102');p='crates/aspis-prover/src/state_only_entropy.rs'
raw=subprocess.check_output(['git','show','HEAD:'+p]);s=raw.decode()
a=s.index('    pub fn generate_for_mask_nonce(');i=s.index('{',a);j=i+1;level=1
while level:
 level+=(s[j]=='{')-(s[j]=='}');j+=1
body=s[a:j]
steps=[('let mut bytes = Zeroizing::new([0u8; 64]);','admit original64 zeroed lifetime, owner and machine address from actual source frame'),
 ('getrandom::fill(bytes.as_mut())?;','borrow original64; OS error exits through its zeroize1.9.0 Drop; fill success restores borrow'),
 ('let mut field_mask_entropy = Zeroizing::new([0u8; 32]);','admit first inner32 zeroed lifetime'),
 ('let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);','admit second inner32 zeroed lifetime'),
 ('field_mask_entropy.copy_from_slice(&bytes[..32]);','copy first32; preserve mutable-borrow restoration'),
 ('leaf_salt_seed.copy_from_slice(&bytes[32..]);','copy second32; preserve mutable-borrow restoration'),
 ('if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed)','short-circuit field test then seed test'),
 ('return Ok(Self {\n                    mask_nonce,\n                    field_mask_entropy,\n                    leaf_salt_seed,\n                });','move both32 owners into returned Self; drop original64; do not fabricate zeroization of moved-from stack copies'),
 ('retry+=1;','increment then scope drops leaf32, field32, original64 before next condition'),
 ('Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)','retry limit error after completed iteration scopes')]
positions=[body.index(x) for x,_ in steps[:-1]]+[body.rindex(steps[-1][0])];assert positions==sorted(positions)
out=dict(evidence_class='structural source statement inventory; actual frame interpretation not supplied',
 source=dict(path=p,blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sha256=hashlib.sha256(raw).hexdigest(),body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest()),
 steps=[dict(source=x,obligation=y) for x,y in steps],
 established='Source creates one original64 and two success-only inner32 lifetimes. Error before inner32 initialization cleans only original64. Successful move is distinct from a destructor call on both32.',
 missing=['No numeric original/inner source-frame address association is present in the extensional extracted Slice/Array values','No proof that arbitrary StackZero.State is an interpretation of a reached Rust machine frame','Original heap/live separation and coherent physical heap must be derived on that actual interpretation','Successful move/copy, returned owner backing and retired stack residues remain L3/V370 work','Actual raw syscall footprint/ABI association remains P'],
 zeroize='deployed1.9.0 law retained for V221/V222 and L3; do not substitute old1.8.1/single-fence law',
 trust_fields_added=[],rows_removed=[])
p=E/'entropy-frame-source.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS original64/inner32 source lifetime inventory; actual spatial interpretation still OPEN')
