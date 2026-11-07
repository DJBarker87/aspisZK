from NMN_formal import *
import difflib

def native(a,target):
 lib='crates/aspis-r1-cost-probe/src/lib.rs';cand='crates/aspis-r1-cost-probe/src/candidate.rs'
 get=lambda n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 orig={lib:get(lib),cand:get(cand)}
 altered={lib:'#![cfg_attr(kani,feature(allocator_api))]\n'+orig[lib],cand:orig[cand]+'\n#[cfg(kani)]\n#[path="NMN_native.rs"]\nmod NMN_native;\n','crates/aspis-r1-cost-probe/src/NMN_native.rs':read_harness('NMN_native.rs')}
 patch=''.join(''.join(difflib.unified_diff(orig.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in orig else '/dev/null',tofile='b/'+n)) for n,v in altered.items())
 (E/'NMN_HARNESSES.patch').write_text(patch);(E/'NMN_HARNESSES.patch.sha256').write_text(sha(patch.encode())+'\n')
 files={'NMN_src/'+n:v for n,v in altered.items()};files['NMN_source_overlays.json']='{}';files['NMN_gate.py']=(E/'NMN_gate.py').read_text()
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMN_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NMN_target','--features','optimized-terminal,program-build,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 files['NMN_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe'))
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 return run(a,'kani',target,['python3','NMN_gate.py','NMN_native_config.json'],files,env)
if __name__=='__main__':
 r=native(*sys.argv[1:]);sys.exit(r['exit_status'])
