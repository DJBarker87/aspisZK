from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
prior=json.loads((E.parent/'slice-d-check-20261104/NFU_NATIVE_INPUTS.json').read_text())
code=prior[C+'NFU_verifier.rs'].replace('NFU','NGM')
# Rename only the parent sidecar module; the original per-property harness names
# and exact corrected nine-word comparisons are retained with provenance.
# Negative controls corrupt a selected observation/child reply and preserve
# all other source-step behaviour; no optional/unreached false assertion.
code=code.replace('let final_state=', 'let mut final_state=')
code=code.replace('let good=match group{', 'if cfg!(NGM_invert){match group{1=>index=index.wrapping_add(1),2=>log.calls+=1,3=>log.before[0]^=1,4=>final_state[0]^=1,5=>log.value[0]^=1,6=>log.value[4]^=1,7=>log.scalar[0]^=1,8=>log.value[0]=0x7fffffff,9=>log.order=255,10=>log.field_ptr=log.field_ptr.wrapping_add(1),11=>log.field_len=31,12=>log.field_index+=1,13=>log.weight_ptr=log.weight_ptr.wrapping_add(1),_=>{}}}\n let expected_reply=if cfg!(NGM_invert)&&group==0{!reply}else{reply};\n let good=match group{')
code=code.replace('0=>if reply{','0=>if expected_reply{').replace('assert!(good != cfg!(NGM_invert));','assert!(good);')
inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());src=subprocess.check_output(['git','show','4bb3b3f:'+C+'verifier.rs'],text=True)
inputs[C+'verifier.rs']=src+'\n#[cfg(kani)] #[path="NGM_verifier.rs"] mod NGM_verifier;\n#[cfg(kani)] #[path="NGM_dot.rs"] mod NGM_dot;\n'
inputs[C+'NGM_dot.rs']=code
for a,b in [('NFU_canonical.rs','NGM_canonical.rs'),('NFU_fast_helpers.rs','NGM_fast_helpers.rs')]:inputs[C+b]=prior[C+a].replace('NFU','NGM')
fast=subprocess.check_output(['git','show','4bb3b3f:'+C+'fast_pairing.rs'],text=True)
fast=fast.replace('    //! No public unchecked constructor. This does NOT change aspis_core::M31.\n','    //! No public unchecked constructor. This does NOT change aspis_core::M31.\n #[cfg(kani)] pub(super) mod NGM_canonical { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NGM_canonical.rs")); }\n',1)
fast+='\n#[cfg(kani)] #[path="NGM_fast_helpers.rs"] pub(crate) mod NGM_helpers;\n'
inputs[C+'fast_pairing.rs']=fast
(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in inputs.items()});(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_DOT_PROVENANCE.json').write_text(json.dumps(dict(source='evidence/slice-d-check-20261104/NFU_NATIVE_INPUTS.json',candidate='NFU_FINISH_CANDIDATE.json; corrected K079 nine-word comparisons, not excluded K078 builtin-memcmp shape',source_sha256=hashlib.sha256((E.parent/'slice-d-check-20261104/NFU_NATIVE_INPUTS.json').read_bytes()).hexdigest(),prefix_change='NFU -> NGM in private source only; original per-property finish_g names retained',method='one native arbitrary-prestate iteration, local full typed EbyKDot receiver, unconstrained whole nine-word update and full Result, canonical byte window at arbitrary j<64; no field multiplication',credit='OPEN until canonical ABI, full loop/callee/adopted-model composition and final replay'),indent=2)+'\n')
