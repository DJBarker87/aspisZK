from NMV_formal import *
import difflib

def program(a,target):
 lib='programs/r1-cost-probe/src/lib.rs';owned='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
 get=lambda n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 orig={lib:get(lib),owned:get(owned)}
 altered={lib:'#![cfg_attr(kani,feature(allocator_api))]\n'+orig[lib],owned:orig[owned]+'\n#[cfg(kani)]\n#[path="NMV_program.rs"]\nmod NMV_program;\n','programs/r1-cost-probe/src/NMV_program.rs':(E/'NMV_program.rs').read_text()}
 altered['programs/r1-cost-probe/src/NMV_parent.rs']=(E/'NMV_parent.rs').read_text()
 patch=''.join(''.join(difflib.unified_diff(orig.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in orig else '/dev/null',tofile='b/'+n)) for n,v in altered.items())
 (E/'NMV_HARNESSES.patch').write_text(patch);(E/'NMV_HARNESSES.patch.sha256').write_text(sha(patch.encode())+'\n')
 files={'NMV_src/'+n:v for n,v in altered.items()};files['NMV_src/programs/r1-cost-probe/src/NMV_parent.rs']=(E/'NMV_parent.rs').read_text();files['NMV_gate.py']=(E/'NMV_gate.py').read_text()
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMV_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMV_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness','r1_pool_adapter::owned::NMV_program::'+target,'--output-format','terse']
 files['NMV_program_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe-program'))
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 return run(a,'kani',target,['python3','NMV_gate.py','NMV_program_config.json'],files,env)
if __name__=='__main__':
 r=program(*sys.argv[1:]);sys.exit(r['exit_status'])
