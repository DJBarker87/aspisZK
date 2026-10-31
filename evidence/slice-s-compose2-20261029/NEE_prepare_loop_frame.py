"""Frame one actual frozen canonicality iteration; erase every added cfg cut."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
case,control=sys.argv[1:];assert case in {'forest','tree'} and control in {'positive','negative'}
path='crates/aspis-statement/src/pool_v1/'+('pair_forest_accounts.rs' if case=='forest' else 'pair_tree_profile.rs')
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
arg='digest' if case=='forest' else 'value'
header=('fn' if case=='forest' else 'pub(crate) fn')+' digest_is_canonical('+arg+': &Digest) -> bool {'
start=frozen.index(header);end=frozen.index('\n}',start)+2
body=frozen[start:end]
assert body.count('    let mut i = 0;')==1 and body.count('        i += 1;')==1
init='\n    #[cfg(kani)]\n    { i = unsafe { NEE_loop_frame::START }; }'
cut='\n        #[cfg(kani)]\n        { unsafe { NEE_loop_frame::END = i; } return true; }'
changedbody=body.replace('    let mut i = 0;','    let mut i = 0;'+init).replace('        i += 1;','        i += 1;'+cut)
assert changedbody.replace(init,'').replace(cut,'')==body
expr=f'''unsafe {{ let i=NEE_loop_frame::START; let good=i>=8||{arg}[i].0<P;
 *r==good && NEE_loop_frame::END==if i<8&&good {{i+1}} else {{i}} }}'''
if control=='negative':expr='!('+expr+')'
attrs='''#[cfg_attr(kani,kani::requires(unsafe {NEE_loop_frame::START<=8 && NEE_loop_frame::END==NEE_loop_frame::START}))]
#[cfg_attr(kani,kani::modifies(unsafe { &mut NEE_loop_frame::END }))]
#[cfg_attr(kani,kani::ensures(|r| '''+expr+'''))]
'''
changed=frozen[:start]+attrs+changedbody+frozen[end:]
hook='\n#[cfg(kani)]\n#[path="NEE_'+case+'_loop_frame.rs"]\nmod NEE_loop_frame;\n'
changed+=hook
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
module='''#![allow(non_snake_case)]
use super::*;
use aspis_core::field::M31;
pub(super) static mut START:usize=0;
pub(super) static mut END:usize=0;
fn d()->Digest {[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof_for_contract(digest_is_canonical)]
#[kani::unwind(2)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn step_frame(){let input=d();let i:usize=kani::any();kani::assume(i<=8);unsafe{START=i;END=i;}let _=digest_is_canonical(&input);}
'''
name='crates/aspis-statement/src/pool_v1/NEE_'+case+'_loop_frame.rs'
patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
base,oraclehook=oracle_parts()
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(base.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in base.splitlines())+oraclehook)
audit=dict(case=case,control=control,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_file=path,source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),native_body_sha256=hashlib.sha256(body.encode()).hexdigest(),cfg_erasure_exact=changedbody.replace(init,'').replace(cut,'')==body,domain='every typed Digest; arbitrary index 0<=i<=8; END initially i; START immutable; one iteration only',modifies='END ghost only; no external/input writes',native_harness='pool_v1::'+('pair_forest_accounts' if case=='forest' else 'pair_tree_profile')+'::NEE_loop_frame::step_frame',patch_sha256=hashlib.sha256(patch.encode()).hexdigest())
(E/('NEE_'+case+'_LOOP_'+control+'.json')).write_text(json.dumps(audit,indent=1)+'\n')
print(audit['native_harness'])
