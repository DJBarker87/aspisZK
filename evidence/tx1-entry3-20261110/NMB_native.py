"""NMB native submissions: actual frozen stage1 contract with full-payload child cuts."""
from NMB_formal import *
import base64,difflib
frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
def native(a,invert=False,target_suffix="NMB_stage1_child_boundary"):
 if target_suffix in ['NMB_array_move_window','NMB_stage1_child_boundary','NMB_array_header_contract','NMB_array_error_contract','NMB_owned_select_contract']:
  gate=json.loads((E/'NMB_INPUT_FIDELITY.json').read_text());assert gate['allowed'] is True
  src=(E/'NMB_owned.rs').read_text();p=src.index('#[kani::modifies(v)]\n#[kani::ensures(|_| !cfg!(NMB_input_invert))]');q=src.index('\n#[kani::modifies(v)]',p+1)
  assert sha(src[p:q].encode())==gate['unit_sha256'],'Changed input contract: recalibrate'
 lib=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/lib.rs']).decode()
 adapter=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode()
 owned=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']).decode()
 attrs='#[cfg_attr(kani,kani::requires(accounts.len()==3 && (data==&[3,10] || data==&[3,11])))]\n#[cfg_attr(kani,kani::ensures(|result| NMB_owned::stage1_post(program_id,accounts,data,result)))]\n#[cfg_attr(kani,kani::modifies(NMB_owned::flag(&accounts[0]),NMB_owned::flag(&accounts[1]),NMB_owned::flag(&accounts[2])))]\n'
 marker='pub(super) fn stage1('
 assert owned.count(marker)==1
 changed={
 'programs/r1-cost-probe/src/lib.rs':'#![cfg_attr(kani,feature(allocator_api))]\n'+lib+'\n#[cfg(kani)]\n#[path="NMB_native.rs"]\nmod NMB_native;\n',
 'programs/r1-cost-probe/src/NMB_native.rs':'extern crate alloc;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n',
 'programs/r1-cost-probe/src/r1_pool_adapter.rs':adapter+'\n#[cfg(kani)]\n#[path="NMB_adapter.rs"]\npub(crate) mod NMB_adapter;\n',
 'programs/r1-cost-probe/src/NMB_adapter.rs':'// Namespace retained solely for strict frozen-overlay validation.\n',
 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs':owned.replace(marker,attrs+marker)+'\n#[cfg(kani)]\n#[path="NMB_owned.rs"]\nmod NMB_owned;\n',
 'programs/r1-cost-probe/src/NMB_owned.rs':(E/'NMB_owned.rs').read_text()}
 originals={'programs/r1-cost-probe/src/lib.rs':lib,'programs/r1-cost-probe/src/r1_pool_adapter.rs':adapter,'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs':owned}
 patch=''.join(''.join(difflib.unified_diff(originals.get(n,'').splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))for n,t in changed.items())
 (E/'NMB_NATIVE.patch').write_text(patch)
 files={'NMB_src/'+n:t for n,t in changed.items()}
 files.update({'NMB_gate.py':(E/'NMB_gate.py').read_text(),'NMB_expected_KMX.patch':frozen['NLF_KMX_copy_stubs.patch'],'NMB_stage1_attrs.txt':attrs})
 env=json.loads((E.parent/'sdk-borrow-20261109/NLF_K044.json').read_text())['env']
 env.update(TMPDIR=B+'/NMB_tmp',CARGO_TARGET_DIR=B+'/NMB_target',CARGO_NET_OFFLINE='true')
 if invert:env['RUSTFLAGS']=env.get('RUSTFLAGS','')+' --cfg '+('NMB_array_badframe' if invert=='frame' else 'NMB_input_invert' if target_suffix.startswith('NMB_input_') else 'NMB_invert')
 target='r1_pool_adapter::owned::NMB_owned::'+target_suffix
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMB_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMB_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 files['NMB_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe-program'))
 return run(a,'kani',target,command=['python3','NMB_gate.py','NMB_native_config.json'],extra=files,env_extra=env)
if __name__=='__main__':
 r=native(sys.argv[1],('frame' if len(sys.argv)>2 and sys.argv[2]=='frame' else len(sys.argv)>2 and sys.argv[2]=='invert'),sys.argv[3] if len(sys.argv)>3 else 'NMB_stage1_child_boundary');sys.exit(r['exit_status'])
