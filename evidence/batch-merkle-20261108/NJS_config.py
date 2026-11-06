from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-batch-merkle-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,kind,target=sys.argv[1:4];invert='--invert' in sys.argv
assert not (E/(a+'.json')).exists()
upload=[];collect=[];env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=B+'/NJS_target')
if kind=='kani':
 upload=['NJS_gate.py','NJS_harness.rs','NJS_KMX.patch','NJS_NHR_stage.py','NJS_SUPPLEMENT.json','NJS_fragments.rs','NJS_FRAGMENT_ASSOCIATION.json'];command=['python3','NJS_gate.py',a+'.json'];collect=[a+'_validation']
 env.update(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJS_invert' if invert else ''))
elif kind=='lean':
 upload=[target+'.lean'];command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','NJS_objects/'+target+'.olean',target+'.lean'];env.update(LEAN_SYSROOT=T,LEAN_PATH=':'.join(json.loads((E/'NJS_PATHS.json').read_text())))
else:raise ValueError(kind)
x=dict(attempt=a,kind=kind,module=target,sources=upload,upload=upload,command=command,collect=collect,timeout=180,env=env,deps_fingerprint={},expected_time='optimized compilation then named native helper/cut' if kind=='kani' else 'focused Lean elaboration')
if kind=='kani':x['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NJS_workspace/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NJS_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness','verifier::candidate::NJS_native::'+target,'--output-format','terse']
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
