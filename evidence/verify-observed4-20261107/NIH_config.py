from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-verify-observed4-20261107';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def write(a,kind,target,flags=''):
 x=dict(attempt=a,kind=kind,module=target,sources=[],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NIH_tmp',LEAN_PATH=':'.join(json.loads((E/'NIH_PATHS.json').read_text()))),timeout=180,expected_time='Focused import elaboration')
 if kind=='lean':
  n='NIH_generated/'+target+'.lean';p=E/n;p.parent.mkdir(exist_ok=True);p.write_text((E/(target+'.lean')).read_text());x['sources']=[n];x['command']=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NIH_generated','-o','NIH_objects/'+target+'.olean',n]
  if target in ['NIH_Driver','NIH_ProofDriver']:x['command']+=['-c','NIH_native/'+target+'.c']
 elif kind=='kani':
  features=','.join(next(p['features'] for p in json.loads((E.parent/'verify-observed3-20261106/NHU_preflight/NHR_GRAPH_CHECK.json').read_text())['features'] if p['name']=='aspis-statement'))
  x.update(root_package='aspis-statement',metadata_features=','.join('aspis-statement/'+f for f in features.split(',')))
  x['sources']=['NIH_gate.py','NIH_SOURCE_PINS.json','NIH_FROZEN_FILE_PINS.json']+['NIH_src/'+n for n in json.loads((E/'NIH_SOURCE_PINS.json').read_text())]
  x['command']=['python3','NIH_gate.py',a+'.json']
  x['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NIH_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NIH_target','--features',features,'--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
  x['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS=('-Copt-level=3 -C link-arg=-Wl,--threads=1 '+flags).strip())
  x['expected_time']='optimized compilation then isolated native transition assertion; no field products'
  x['collect']=[a+s for s in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']]
 else:raise ValueError(kind)
 (E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
if __name__=='__main__':write(*sys.argv[1:])
