"""Check source association of the native entropy iteration error branch."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda b:hashlib.sha256(b).hexdigest()
project=next(v for v in json.load(open(E/'native-sources.json'))['project'] if v['path'].endswith('state_only_entropy.rs'))
src=subprocess.check_output(['git','show','HEAD:'+project['path']]);assert sha(src)==project['sha256']
text=src.decode();start=text.index('pub fn generate_for_mask_nonce(');a=text.index('{',start);b=a+1;depth=1
while depth:
 depth+=(text[b]=='{')-(text[b]=='}');b+=1
body=text[a:b]
source_steps=[
 ('let mut bytes = Zeroizing::new([0u8; 64]);','PV_EVH_NativeZeroWrappers.constructor_native; PV_EVH_StackAdmission.enter','source initializer; original stack region remains a machine-frame association obligation'),
 ('getrandom::fill(bytes.as_mut())?;','PV_EVH_NativeEntropyBorrow.array_borrow; PV_EVH_NativeEntropyIterationError.error_native','original mutable array borrow, full post-buffer, ordinary error drop'),
 ('let mut field_mask_entropy = Zeroizing::new([0u8; 32]);','OPEN success continuation','not reached on the proved error branch'),
 ('let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);','OPEN success continuation','not reached on the proved error branch'),
 ('retry+=1;','OPEN retry continuation','not reached on the proved error branch')]
steps=[]
for fragment,law,status in source_steps:
 assert body.count(fragment)==1
 steps.append(dict(source=fragment,law=law,status=status))
# The extraction remains byte-identical to its authoritative retained source.
prep=json.load(open(E/'prepare-PV_EVH_NativeEntropyIteration.json'))['result']
f=next(v['source'] for v in prep['project_checks'] if v['module']=='R1Z.ProverRwFullFuns')
raw=subprocess.check_output(['git','show',f['revision']+':'+f['path']]);assert sha(raw)==f['source_sha256']
lean=raw.decode();assert 'let bytes1 := as_mut_back s1' in lean
for theorem,module in [('source_error','NativeEntropyIteration'),('run_step','NativeEntropyIteration'),('error_native','NativeEntropyIterationError')]:
 t=Path('lean/PV_EVH_'+module+'.lean').read_text();assert 'theorem '+theorem in t and '#print axioms '+theorem in t
result=dict(evidence_class='structural source association (own-1) plus actual extracted body branch equality',
 source=dict(path=project['path'],sha256=project['sha256'],method_body=body,method_body_sha256=sha(body.encode())),
 extraction=f,steps=steps,selection='opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)',
 borrowed_restoration='PV_EVH_NativeEntropyBorrow.restore_array retains arbitrary supplied equal-extent buffer',
 actual_body='ProverRwFull.aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body',
 scope='ordinary entropy-error iteration only; not the complete entropy loop or proof-account entry',
 retained=['actual full residual family provenance','native getrandom driver association, including every partial-fill outcome','actual stack-frame key/address provenance, exclusivity and heap separation','success, retry, inner32 and later secret disposal','allocator and diagnostic fidelity','callback integration','full native entry, trace links and (v-prime) nonemptiness','V370 and L3 joint observation'],
 rows_removed=[],trust_fields_added=[])
out=E/'entropy-iteration-binding.json'
if '--check' in sys.argv:assert json.load(open(out))==result
else:out.write_text(json.dumps(result,indent=2)+'\n')
print('PASS source entropy error iteration association; complete native entry remains OPEN')
