#!/usr/bin/env python3
"""Reuse complete frozen native constructor fixture; replace only proof module."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent;O=Path(sys.argv[1]).resolve()
subprocess.run(['python3',str(R/'tools/s1-native-prepared-claim-20261025/prepare.py'),'--out',str(O)],cwd=R,check=True,stdout=subprocess.DEVNULL)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P=O/'min/src/prepared_claim_native';verifier=P/'verifier.rs';before=verifier.read_text()
assert 'fn prepared_claim<'in before and '#[path="proofs.rs"]mod proofs;'in before
reference_path=D/('reference-zero-copy.rs'if '--zero-copy'in sys.argv[2:]else'reference.rs')
reference=reference_path.read_text()
assert reference.count('fn owned_scalar(')==reference.count('fn owned_push(')==1
assert 'claims:&[[K;29];3]'in reference and 'g:&[E;29]'in reference
verifier.write_text(before+'\n#[cfg(kani)] mod paired_reference {\nuse super::*;\n'+reference+'\n}\n')
proof=D/('profile.rs'if '--profile'in sys.argv[2:]else'proofs.rs')
(P/'proofs.rs').write_bytes(proof.read_bytes())
revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
frozen=subprocess.check_output(['git','show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R,text=True)
core_updates={}
for path in subprocess.check_output(['git','ls-tree','-r','--name-only',revision,'crates/aspis-core'],cwd=R,text=True).splitlines():
 target=O/'core-workspace'/path
 if path.endswith('.rs')and target.exists():
  value=subprocess.check_output(['git','show',revision+':'+path],cwd=R)
  if target.read_bytes()!=value:
   core_updates[path]={'before_sha256':sha(target),'after_sha256':hashlib.sha256(value).hexdigest()}
   target.write_bytes(value)
def item(text,key):
 start=text.index(key);end=text.index('{',start)+1;depth=1
 while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
 return text[start:end]
assert item(before,'fn prepared_claim<')==item(frozen,'fn prepared_claim<')
assert item(before,'fn prepared_claim<')in verifier.read_text()
binding={'schema':'focused-extractor-proof-packet-v1','release_revision':revision,
 'original_verifier_sha256':hashlib.sha256(before.encode()).hexdigest(),
 'original_claim':item(before,'fn prepared_claim<'),'reference_sha256':sha(reference_path),
 'zero_copy_reference':'--zero-copy'in sys.argv[2:],
 'proof_sha256':sha(proof),'actual_native_body_unchanged':True,'current_freeze_core_updates':core_updates,
 'proof_mode':'one-pass characteristic profile'if '--profile'in sys.argv[2:]else'paired replay',
 'reference_changes':'Borrow private scalar/push/sum arrays; retain complete original borrowed public ABI and owned Dot state.',
 'leaf_boundary':'Common ordered normal-return tape for full push/finish/field/mul/add carriers; all first rejection ordinals0..174. Field records exact slice pointer/length/index. No UF recursion or by-value arrays per inner iteration.',
 'remaining':'Actual leaf installation, native panic/abort/allocation/runtime/SDK/oracle/release association and extracted-reference join remain explicit.'}
(O/'paired-binding.json').write_text(json.dumps(binding,indent=2)+'\n')
files={str(p.relative_to(O)):sha(p)for p in sorted(O.rglob('*'))if p.is_file()}
(O/'plan.json').write_text(json.dumps({'files':files},indent=2)+'\n')
print(json.dumps({'workspace':str(O),'files':len(files)}))
