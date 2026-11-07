from NLW_formal import *
import base64,difflib

def native(a,target):
 frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
 libpath='crates/aspis-r1-cost-probe/src/lib.rs';candpath='crates/aspis-r1-cost-probe/src/candidate.rs'
 get=lambda n: subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 orig={libpath:get(libpath),candpath:get(candpath)}
 altered={libpath:'#![cfg_attr(kani,feature(allocator_api))]\n'+orig[libpath],candpath:orig[candpath]+'\n#[cfg(kani)]\n#[path="NLW_native.rs"]\nmod NLW_native;\n','crates/aspis-r1-cost-probe/src/NLW_native.rs':(E/'NLW_native.rs').read_text()}
 patch=''.join(''.join(difflib.unified_diff(orig.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in orig else '/dev/null',tofile='b/'+n)) for n,v in altered.items());(E/'NLW_native.patch').write_text(patch)
 files={'NLW_src/'+n:v for n,v in altered.items()}
 files.update({'NLW_gate.py':(E/'NLW_gate.py').read_text(),'NLW_expected_KMX.patch':frozen['NLF_KMX_copy_stubs.patch'],'NLW_FROZEN_PINS.json':frozen['NLF_FROZEN_PINS.json'],'NLW_EXTRA_PINS.json':json.dumps({n:z['sha256'] for n,z in json.loads((E.parent/'tx2-entry2-20261110/NLM_NATIVE_EXTRA_PINS.json').read_text()).items()})})
 for section in frozen['NLF_KMX_copy_stubs.patch'].split('diff --git ')[1:]:
  lines=section.splitlines();dest=lines[0].split(' b/',1)[1]
  files['NLW_src/'+dest]='\n'.join(l[1:] for l in lines if l.startswith('+') and not l.startswith('+++'))+'\n'
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NLW_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NLW_target','--features','optimized-terminal,program-build,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 files['NLW_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe'))
 return run(a,'kani',target,['python3','NLW_gate.py','NLW_native_config.json'],files,env)
if __name__=='__main__':
 r=native(*sys.argv[1:]);sys.exit(r['exit_status'])
