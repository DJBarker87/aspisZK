"""Install cfg(kani) contracts on actual frozen functions in private scratch."""
from NMD_native import run,E,B,subprocess,json,lzma,difflib
import sys

def native(a,target):
 frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
 lib='crates/aspis-r1-cost-probe/src/lib.rs';cand='crates/aspis-r1-cost-probe/src/candidate.rs'
 original={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True) for n in [lib,cand]}
 specs=json.loads((E/'NMD_ACTUAL_CONTRACTS.json').read_text());body=original[cand];lines=[]
 for signature,attributes in specs.items():
  assert body.count(signature)==1,signature
  text=''.join(attributes);body=body.replace(signature,text+signature,1);lines+=attributes
 altered={lib:'#![cfg_attr(kani,feature(allocator_api))]\n'+original[lib],cand:body+'\n#[cfg(kani)]\n#[path="NMD_native.rs"]\nmod NMD_native;\n','crates/aspis-r1-cost-probe/src/NMD_native.rs':(E/'NMD_actual.rs').read_text()}
 patch=''.join(''.join(difflib.unified_diff(original.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in original else '/dev/null',tofile='b/'+n)) for n,s in altered.items());(E/'NMD_ACTUAL.patch').write_text(patch)
 files={'NMD_src/'+n:v for n,v in altered.items()};files['NMD_source_overlays.json']=json.dumps({cand:lines})
 for frozen_path in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','crates/aspis-r1-cost-probe/src/verifier.rs']:
  files['NMD_src/'+frozen_path]=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+frozen_path],text=True)
 files.update({'NMD_gate.py':(E/'NMD_gate.py').read_text(),'NMD_expected_KMX.patch':frozen['NLF_KMX_copy_stubs.patch'],'NMD_FROZEN_PINS.json':frozen['NLF_FROZEN_PINS.json'],'NMD_EXTRA_PINS.json':json.dumps({n:z['sha256'] for n,z in json.loads((E.parent/'tx2-entry2-20261110/NLM_NATIVE_EXTRA_PINS.json').read_text()).items()})})
 for section in frozen['NLF_KMX_copy_stubs.patch'].split('diff --git ')[1:]:
  ls=section.splitlines();files['NMD_src/'+ls[0].split(' b/',1)[1]]='\n'.join(l[1:] for l in ls if l.startswith('+') and not l.startswith('+++'))+'\n'
 env=dict(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NMD_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NMD_target','--features','optimized-terminal,program-build,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 if (E/'NMD_CBMC_ARRAY_MODE').exists():cmd+=['--cbmc-args','--no-array-field-sensitivity']
 extra_path=E/'NMD_EXTRA_CONTRACTS.json'
 if extra_path.exists():
  overlays={cand:lines}
  for path,functions in json.loads(extra_path.read_text()).items():
   raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True);original[path]=raw;added=[]
   for signature,attrs in functions.items():
    assert raw.count(signature)==1;raw=raw.replace(signature,''.join(attrs)+signature,1);added+=attrs
   files['NMD_src/'+path]=raw;overlays[path]=added
  files['NMD_source_overlays.json']=json.dumps(overlays)
 files['NMD_native_config.json']=json.dumps(dict(attempt=a,native_command=cmd,root_package='aspis-r1-cost-probe'))
 return run(a,'kani',target,['python3','NMD_gate.py','NMD_native_config.json'],files,env)
if __name__=='__main__':native(*sys.argv[1:])
