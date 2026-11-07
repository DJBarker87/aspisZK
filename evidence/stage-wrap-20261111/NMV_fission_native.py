from NMV_formal import *
from NMV_program import artifact
import difflib

def native(a,target,parent=False,parent_base=None):
 lib='programs/r1-cost-probe/src/lib.rs';owned='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
 get=lambda n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 orig={lib:get(lib),owned:get(owned)}
 program=artifact('NMV_program.rs')+'\n#[path="NMV_Fission.rs"]\nmod NMV_Fission;\n#[path="NMV_FissionHarness.rs"]\nmod NMV_FissionHarness;\n'
 altered={lib:'#![cfg_attr(kani,feature(allocator_api))]\n'+orig[lib],owned:orig[owned]+'\n#[cfg(kani)]\n#[path="NMV_program.rs"]\nmod NMV_program;\n','programs/r1-cost-probe/src/NMV_program.rs':program,'programs/r1-cost-probe/src/NMV_parent.rs':artifact('NMV_parent.rs'),'programs/r1-cost-probe/src/NMV_Fission.rs':(E/'NMV_Fission.rs').read_text(),'programs/r1-cost-probe/src/NMV_FissionHarness.rs':(E/'NMV_FissionHarness.rs').read_text()}
 if parent:
  if parent_base:
   import lzma
   idx=json.loads((E/'NMV_INPUTS.json').read_text());h=idx['attempts'][parent_base]['NMV_src/programs/r1-cost-probe/src/NMV_FissionHarness.rs']
   raw=lzma.decompress((E/idx['objects'][h]['path']).read_bytes());assert sha(raw)==h
   altered['programs/r1-cost-probe/src/NMV_FissionHarness.rs']=raw.decode()
  altered['programs/r1-cost-probe/src/NMV_ParentMutants.rs']=(E/'NMV_ParentMutants.rs.pending').read_text()
  altered['programs/r1-cost-probe/src/NMV_FissionHarness.rs']+='\n'+(E/'NMV_ParentMutantHarness.rs.pending').read_text()
 patch=''.join(''.join(difflib.unified_diff(orig.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in orig else '/dev/null',tofile='b/'+n)) for n,v in altered.items())
 patchname='NMV_PARENT_HARNESSES.patch' if parent else 'NMV_FISSION_HARNESSES.patch'
 (E/patchname).write_text(patch)
 (E/(patchname+'.sha256')).write_text(sha(patch.encode())+'\n')
 files={'NMV_src/'+n:v for n,v in altered.items()};files['NMV_gate.py']=(E/'NMV_gate.py').read_text()
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMV_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NMV_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness','r1_pool_adapter::owned::NMV_program::'+('' if target.startswith('NMV_copy_') else 'NMV_FissionHarness::')+target,'--output-format','terse']
 files['NMV_fission_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe-program'))
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 return run(a,'kani',target,['python3','NMV_gate.py','NMV_fission_config.json'],files,env)
if __name__=='__main__':
 r=native(*sys.argv[1:]);sys.exit(r['exit_status'])
