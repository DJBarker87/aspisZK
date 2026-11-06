from NLM_formal import *
import base64

def native(a,target):
 assert a.startswith('NLM_K') and 1<=int(a[-3:])<=999
 frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
 lib=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/lib.rs']).decode()
 owned=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']).decode()
 patch=(E/'NLM_native.patch').read_text()
 source=''.join(l[1:] for l in patch.split('+++ b/programs/r1-cost-probe/src/NLM_native.rs\n',1)[1].splitlines(True) if l.startswith('+'))
 files={'NLM_src/programs/r1-cost-probe/src/lib.rs':'#![cfg_attr(kani,feature(allocator_api))]\n'+lib,
  'NLM_src/programs/r1-cost-probe/src/r1_pool_adapter_owned.rs':owned+'\n#[cfg(kani)]\n#[path="NLM_native.rs"]\nmod NLM_native;\n',
  'NLM_src/programs/r1-cost-probe/src/NLM_native.rs':source,
  'NLM_gate.py':(E/'NLM_gate.py').read_text(),
  'NLM_expected_KMX.patch':frozen['NLF_KMX_copy_stubs.patch']}
 for section in frozen['NLF_KMX_copy_stubs.patch'].split('diff --git ')[1:]:
  lines=section.splitlines();dest=lines[0].split(' b/',1)[1]
  files['NLM_src/'+dest]='\n'.join(l[1:] for l in lines if l.startswith('+') and not l.startswith('+++'))+'\n'
 files['NLM_FROZEN_PINS.json']=frozen['NLF_FROZEN_PINS.json']
 files['NLM_EXTRA_PINS.json']=json.dumps({n:z['sha256'] for n,z in json.loads((E/'NLM_NATIVE_EXTRA_PINS.json').read_text()).items()})
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NLM_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NLM_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 files['NLM_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe-program'))
 rc=run(a,'kani',target,['python3','NLM_gate.py','NLM_native_config.json'],files,env)

 return rc
if __name__=='__main__':
 r=native(*sys.argv[1:]);sys.exit(r['exit_status'])
