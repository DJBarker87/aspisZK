from NMD_formal import *
import base64,difflib

def native(a,target):
 frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
 libpath='programs/r1-cost-probe/src/lib.rs';candpath='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
 get=lambda n: subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 orig={libpath:get(libpath),candpath:get(candpath)}
 altered={libpath:'#![cfg_attr(kani,feature(allocator_api))]\n'+orig[libpath],candpath:orig[candpath]+'\n#[cfg(kani)]\n#[path="NMD_program.rs"]\nmod NMD_program;\n','programs/r1-cost-probe/src/NMD_program.rs':(E/'NMD_program.rs').read_text()}
 patch=''.join(''.join(difflib.unified_diff(orig.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in orig else '/dev/null',tofile='b/'+n)) for n,v in altered.items());(E/'NMD_program.patch').write_text(patch)
 files={'NMD_src/'+n:v for n,v in altered.items()}
 files['NMD_source_overlays.json']='{}'
 files.update({'NMD_gate.py':(E/'NMD_gate.py').read_text(),'NMD_expected_KMX.patch':frozen['NLF_KMX_copy_stubs.patch'],'NMD_FROZEN_PINS.json':frozen['NLF_FROZEN_PINS.json'],'NMD_EXTRA_PINS.json':json.dumps({n:z['sha256'] for n,z in json.loads((E.parent/'tx2-entry2-20261110/NLM_NATIVE_EXTRA_PINS.json').read_text()).items()})})
 for section in frozen['NLF_KMX_copy_stubs.patch'].split('diff --git ')[1:]:
  lines=section.splitlines();dest=lines[0].split(' b/',1)[1]
  files['NMD_src/'+dest]='\n'.join(l[1:] for l in lines if l.startswith('+') and not l.startswith('+++'))+'\n'
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMD_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMD_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 files['NMD_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe-program'))
 return run(a,'kani',target,['python3','NMD_gate.py','NMD_native_config.json'],files,env)
if __name__=='__main__':
 r=native(*sys.argv[1:]);sys.exit(r['exit_status'])
